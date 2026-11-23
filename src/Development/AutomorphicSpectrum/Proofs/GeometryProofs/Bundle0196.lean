module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0194
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0190
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfDiv
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0195
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLattice

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationEigenFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan

theorem span_eq_eigSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K))
    (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K))
    (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y))
    (m' : SABMap tK T (spMap (algebraMap V K))) (n : ℕ) (σ : E →+* K) (σi : 𝓞 E →+* K) (b : Fin n → Fin g → K),
    spMap (algebraMap V K) ≫ z = y ≫ Y.j → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →
    (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    Z.M.lat.IsFrameAt ℓ ⟨_, h₂⟩ → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) →
    (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) →
    MU.IsActOf Xo.univ.t.act.act ρK → (∀ a : 𝓞 E, σi a = σ (a : E)) →
    IsIntFrame m m' σi (fun i => MU.pt (b i)) → LinearIndependent K b →
    Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z V K _ _ _ _ _ _ y z h₁ h₂ ψ g ℓ ρK MU MY T tK m m' n σ σi b hz hreg hint hfr₂ hfr₁ hsame hval hact hσ hif hli
  obtain ⟨ML, hML⟩ := (LieMove.main K Xo.X (under y) Xo.univ.t.G tK.G m.φ (Fin g → K) m.cart).1 MU
  obtain ⟨φ₁, hφ₁, htr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model E H D l Xo c O β Y K y tK m
  obtain ⟨σV, vV, hσV, hfr, hu⟩ := hif
  have hρ : ML.IsActOf tK.act.act ρK := by
    intro r e
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hML, hact r e, Over.comp_left, Over.comp_left, Category.assoc, m.act r, ← Category.assoc, hML]
    · rw [Over.w (ML.pt (ρK r e)), Over.comp_left, Category.assoc, Over.w (tK.act.act r), Over.w (ML.pt e)]
  have hepi : Epi (CommRingCat.ofHom (algebraMap V K)) := IsLocalization.epi (nonZeroDivisors V) K
  have hmono : Mono (spMap (algebraMap V K)) := by
    exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom (algebraMap V K)).op
  have hb : ∀ i, (ML.pt (b i)).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left := by
    intro i
    obtain ⟨u, hu1, hu2⟩ := hu i
    have hw : u ≫ tK.G.hom = (ML.pt (b i)).left ≫ tK.G.hom := by
      rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, ← m'.cart.1.w, ← Category.assoc, hu2,
        Category.assoc, Over.w (vV i), Over.w (ML.pt (b i))]
      exact (LieTangent.spec_dual_alg _ |>.trans (by simp))
    have : u = (ML.pt (b i)).left := m.cart.1.hom_ext (hu1.trans (hML _).symm) hw
    rw [← this]; exact hu2
  have key := _root_.GlobalTheory.CompanionTheory.Ar.Flat.EigLin.mem_span_iff V K T.G tK.G m'.φ (𝓞 E) T.act tK.act g n ML ρK σV vV b m'.cart m'.act hρ hfr hb
  have cast : ∀ (x x' : Sp K ⟶ Y.X) (_ : x = x') (M : LieModel Y.t.G x' (Fin g → K)),
      ∃ MC : LieModel Y.t.G x (Fin g → K), ∀ e, (MC.pt e).left = (M.pt e).left := by
    rintro _ _ rfl M
    exact ⟨M, fun _ => rfl⟩
  obtain ⟨MC, hMC⟩ := cast _ _ hz MY
  have hfib := _root_.GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V K (y ≫ Y.j) z h₁ h₂ ψ g ℓ MY MC hz hMC Z.gen hreg hint hfr₂ hval
  have hsm := Y.t.semi.smooth
  have h₁' : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) := by
    have : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z = y ≫ Y.j := hz
    rw [this]; exact h₁
  have hL : ∀ w, w ∈ stdLat V K g ↔ ∃ a : epsAt (𝟙 (Sp V)) ⟶ T.G, IsTanAt T.G (𝟙 _) a ∧
      (ML.pt w).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ a.left := by
    intro w
    have hA := GlobalTheory.T.semiabelian_extension_over_dvr V K Y.X Y.t.G T.G tK.G z m'.φ φ₁ Y.t.semi T.semi m'.cart (by rw [hz]; exact hφ₁) (ML.pt w) (ML.tan w)
    have hF := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V z K (Fin g → K) MC Z.gen hsm h₂ h₁' w
    rw [hfib] at hF
    rw [hF, hA]
    have e : (ML.pt w).left ≫ φ₁ = (MC.pt w).left := by
      rw [hMC]; exact htr _ _ _ (hsame w) (hML w)
    rw [e]
  ext w
  rw [key w, ← hL w]
  show _ ↔ w ∈ stdLat V K g ⊓ (HT.eigSp ρK σ).restrictScalars V
  rw [Submodule.mem_inf]
  refine and_congr Iff.rfl ?_
  have : ∀ r, algebraMap V K (σV r) = σ (r : E) := fun r => by
    rw [← hσ r, ← hσV]; rfl
  simp [HT.eigSp, Submodule.mem_iInf, sub_eq_zero, this]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFinitePartMulConstant
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.LateralTheory

theorem ringHom_ext_of_isFractionRing {V K L : Type} [CommRing V] [IsDomain V] [Field K] [Field L] [Algebra V K]
    [IsFractionRing V K] (φ ψ : L →+* K) (θ : V →+* L) (h₁ : φ.comp θ = algebraMap V K)
    (h₂ : ψ.comp θ = algebraMap V K) : φ = ψ := by
  have e₁ : ∀ v, φ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₁ v
  have e₂ : ∀ v, ψ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₂ v
  ext c
  obtain ⟨v, w, hw0, hc⟩ := IsFractionRing.div_surjective (A := V) (φ c)
  have hw : algebraMap V K w ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hw0
  have hθ : θ w * c = θ v := φ.injective (by
    rw [map_mul, e₁, e₁, ← hc]
    field_simp)
  have h3 := congrArg ψ hθ
  rw [map_mul, e₂, e₂] at h3
  rw [← hc, div_eq_iff hw, ← h3, mul_comm]

theorem point_ext {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of V))
    (f g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hf : f ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (x y : Spec (CommRingCat.of (FractionRing V))) (h : f x = g y) : f = g := by
  obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective f
  obtain ⟨⟨w, ψ⟩, hw⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hw
  have hzw : z = w := by
    have h1 : f x ∈ Set.range (X.fromSpecResidueField z) := by
      rw [← hz]; exact ⟨_, rfl⟩
    have h2 : g y ∈ Set.range (X.fromSpecResidueField w) := by
      rw [← hw]; exact ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at h1 h2
    rw [h] at h1
    exact h1.symm.trans h2
  subst hzw
  let θ : CommRingCat.of V ⟶ X.residueField z := Spec.preimage (X.fromSpecResidueField z ≫ π)
  have hθ : Spec.map θ = X.fromSpecResidueField z ≫ π := Spec.map_preimage _
  have h₁ : θ ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hz, hf]
  have h₂ : θ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hw, hg]
  have hφψ : φ = ψ := by
    apply CommRingCat.hom_ext
    exact ringHom_ext_of_isFractionRing (V := V) φ.hom ψ.hom θ.hom
      (congrArg CommRingCat.Hom.hom h₁) (congrArg CommRingCat.Hom.hom h₂)
  rw [← hz, ← hw, hφψ]

variable {V : Type} [CommRing V] [IsDomain V] {T : Type} [CommGroup T]

theorem toUnit_genPt_left : (toUnit (genPt V)).left =
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
  simpa using Over.w (toUnit (genPt V))

theorem section_ext (Γ : QFGroup V T) (σ τ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G)
    (h : toUnit (genPt V) ≫ σ = toUnit (genPt V) ≫ τ) : σ = τ := by
  haveI := Γ.separated
  haveI hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V (FractionRing V)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]
      exact bot_le)⟩
  have h' := congrArg Over.Hom.left h
  simp only [Over.comp_left, toUnit_genPt_left] at h'
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of V)) Γ.G.hom
    ((Over.w σ).trans (Over.w τ).symm)
    (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h')

theorem exists_pt_of_section (Γ : QFGroup V T) (σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G) :
    ∃ t, toUnit (genPt V) ≫ σ = Γ.pt t := by
  let c := toUnit (genPt V) ≫ σ
  let x₀ : Spec (CommRingCat.of (FractionRing V)) := default
  have hover : ∀ c' : genPt V ⟶ Γ.G, c'.left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := fun c' => Over.w c'
  have hgen : (Γ.G.hom (c.left x₀)).asIdeal = ⊥ := by
    have e : Γ.G.hom (c.left x₀) =
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) x₀ := by
      rw [← hover c]; rfl
    have hx₀ : x₀.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top x₀.asIdeal).resolve_right x₀.isPrime.ne_top
    rw [e]
    change Ideal.comap (algebraMap V (FractionRing V)) x₀.asIdeal = ⊥
    rw [hx₀]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  refine ⟨t, Over.OverMorphism.ext ?_⟩
  exact point_ext Γ.G.hom _ _ (hover _) (hover _) x₀ x hx.symm

end GlobalTheory.CompanionTheory.Ar.BT.LateralTheory
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablished
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem m2Model_holds : RootLineDeRhamModel := _root_.GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve _root_.GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem flat_mul_semiAbelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G],
    IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left :=
  PositivityTheory.HtPt.Twhopf.mul_flat

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightEstimateStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_height_estimate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∈ SS → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), ∀ s : CMType H ⊕ CMType H, Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC ≤ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC ∧ ∃ D : T.V, (p : ℝ) ^ (-((padicValInt p (discr E) : ℝ) / Module.finrank ℚ E)) ≤ FinRd.absT p la T e (algebraMap T.V T.Fr D) ∧ ∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC, D • w ∈ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_finite_cover_torus : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open | exact GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open | (intros; apply GlobalTheory.CompanionTheory.Ar.StratOpen.strat_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLatticeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_lie_lattice : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | exact GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | (intros; apply GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full <;> assumption)
end

