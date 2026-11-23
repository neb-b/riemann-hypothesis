module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_modelPoint_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y p κ V K _ _ _ _ _ _ j βK y hκ hj hjκ hy
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hmem : ∀ o : O, (βK.comp β) o ∈ (algebraMap V K).range := by
    intro o
    refine (hj _).1 ?_
    have h1 : j (βK (β o)) = κ (β o) := by rw [← hjκ]; rfl
    simp only [RingHom.comp_apply]
    rw [h1]
    exact (hκ _).2 ⟨o, rfl⟩
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h),
        (algebraMap V K).rangeRestrict_surjective⟩
  let b : O →+* V := e.symm.toRingHom.comp ((βK.comp β).codRestrict _ hmem)
  have hb : (algebraMap V K).comp b = βK.comp β := by
    ext o
    have h2 : e (b o) = (βK.comp β).codRestrict _ hmem o := e.apply_symm_apply _
    exact congrArg Subtype.val h2
  have hsq : (y ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp b)) := by
    rw [hb]
    have h3 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
      simp only [Model.j, Category.assoc]
      rw [pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [Category.assoc, h3, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨z, ⟨hz, _⟩, _⟩ := existsUnique_valuationRing_lift O V K b Y.X Y.s (y ≫ Y.j) hsq
  exact ⟨z, hz⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {Em : Type}
  [AddCommGroup Em] [Module R Em]

theorem isComb_pt_iff (M : LieModel G x Em) {n : ℕ} (b : Fin n → Em) (cf : Fin n → R) (w : epsAt x ⟶ G) :
    IsComb cf (fun i => M.pt (b i)) w ↔ w = M.pt (∑ i, cf i • b i) := by
  have hsum : M.pt (∑ i, cf i • b i) = (List.ofFn fun i => M.pt (cf i • b i)).prod :=
    GlobalTheory.CompanionTheory.Ar.CombEig.pt_sum M fun i => cf i • b i
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hue : u = fun i => M.pt (cf i • b i) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu i, M.smul])
    rw [hsum, hue]
  · rintro rfl
    exact ⟨fun i => M.pt (cf i • b i), fun i => M.smul _ _, hsum⟩

theorem isEigVec_pt_iff {Oe : Type} [CommRing Oe] (M : LieModel G x Em) (act : OAct Oe G)
    {ρ : Oe →+* Module.End R Em} (τ : Oe →+* R) (hρ : M.IsActOf act.act ρ) (e : Em) :
    IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  have hmem : e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [hmem]
  constructor
  · intro h a
    exact M.inj (Over.OverMorphism.ext (by rw [hρ a e, M.smul]; exact h.2 a))
  · intro h
    exact ⟨M.tan e, fun a => by rw [← hρ a e, h a, M.smul]⟩

theorem isEigFrame_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  intro S R _ G _ _ x Em _ _ M Oe _ act ρ τ n b hρ
  have eig := isEigVec_pt_iff M act τ hρ
  have key := isComb_pt_iff M b
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).1 (h1 i), fun e he => ?_⟩
    obtain ⟨c, hc, hu⟩ := h2 (M.pt e) ((eig e).2 he)
    exact ⟨c, M.inj ((key c _).1 hc), fun c' hc' => hu c' ((key c' _).2 (congrArg M.pt hc'))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).2 (h1 i), fun w hw => ?_⟩
    obtain ⟨e, rfl⟩ := M.onto w hw.1
    obtain ⟨c, hc, hu⟩ := h2 e ((eig e).1 hw)
    exact ⟨c, (key c _).2 (congrArg M.pt hc), fun c' hc' => hu c' (M.inj ((key c' _).1 hc'))⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.exists_isBaseChange_of_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F :=
  @PositivityTheory.UnitarySelfGeneration.bt_exists_bc

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCompatibleLieModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  intro X Ω _ ξ G G' _ _ GΩ _ φ φ' h h' V _ _ M
  obtain ⟨M₀, h₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G GΩ φ V h).1 M
  obtain ⟨M', h₁⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G' GΩ φ' V h').2 M₀
  exact ⟨M', fun e => ⟨M₀.pt e, h₀ e, h₁ e⟩⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEmbLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (h : z ^ 2 = -(d : ℂ)) : starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq hd h

theorem exists_emb_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l) (κ : c.F →+* ℂ) (lab : CMType H ⊕ CMType H), ∃ s : E →+* ℂ, κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) ∧ ∀ ρ : c.F, (ρ : ℂ) = H.rt0 → s (H.rt : E) = Sum.elim (fun _ => κ ρ) (fun _ => -κ ρ) lab := by
  intro E _ _ _ H l c κ lab
  rcases lab with τ | τ
  · refine ⟨κ.comp (τ.1.codRestrict c.F (c.conj τ.1)), rfl, fun ρ hρ => ?_⟩
    show κ _ = κ ρ
    congr 1
    apply Subtype.ext
    exact τ.2.trans hρ.symm
  · refine ⟨κ.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (IsCMField.complexConj E : E →+* E)), ?_, fun ρ hρ => ?_⟩
    · refine RingHom.ext fun a => ?_
      show κ _ = κ _
      congr 1
      apply Subtype.ext
      show τ.1 ((H.bar a : 𝓞 E) : E) = τ.1 (IsCMField.complexConj E (a : E))
      rw [H.bar_eq]
    · show κ _ = -κ ρ
      rw [← map_neg]
      congr 1
      apply Subtype.ext
      show τ.1 (IsCMField.complexConj E (H.rt : E)) = -(ρ : ℂ)
      rw [IsCMField.complexEmbedding_complexConj, τ.2, hρ]
      exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldPointLiftsGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_point_lifts_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  exact @PositivityTheory.HtPt.Ml.lift_generic_point
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable def regAtEquivStalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (q : Cpt ξ) : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
  RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun _ _ e => h.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩

theorem isLocalRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  intro X Ω _ ξ h q
  exact (regAtEquivStalk h q).isLocalRing

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
namespace GenericFibreProof

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  obtain ⟨N, i, hi, hs⟩ := hp
  haveI := hi
  haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
      (MvPolynomial (Fin (N + 1)) O) :=
    haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
        (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have hsurj : Function.Surjective
      (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)) := by
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm
  haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  haveI : LocallyOfFiniteType (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : QuasiCompact (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : LocallyOfFiniteType s := by
    rw [← hs]
    infer_instance
  haveI : QuasiCompact s := by
    rw [← hs]
    infer_instance
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO h v hv
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.flat
  haveI := Y.jQ_open
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj
  have hβ : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O c.F
  let z0 : Sp c.F := IsLocalRing.closedPoint c.F
  have hgen : (spMap β z0).asIdeal = ⊥ := by
    rw [spMap_field_pt]
    exact (RingHom.injective_iff_ker_eq_bot β).mp hβ
  have hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal := by
    rw [hgen]
    exact bot_le
  have hspec : spMap β z0 ⤳ Y.s v := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback v z0 hv'
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  refine ⟨w, ?_⟩
  rw [← hq, ← hw]
  simp [Model.j]

end GenericFibreProof

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_in_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  exact @GenericFibreProof.generic_points_range_local
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimes
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem linked_two_levels : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  intro hseg hM3 hTriv E _ _ _ H D l Xo c O₀ _ β Y S S₀ _ _ M instK 𝔐 Fl R hTL hloc φ hφ
  obtain rfl : instK = (fun a b => Classical.propDecidable (a = b) : DecidableEq M.K) := Subsingleton.elim _ _
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hvert⟩ := hTL
    exact hvert
  · obtain ⟨hded, hfin, hinj, hcst, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 (dimFl (CMType H) (D.p + D.q)) M.arith (integralClosure ℤ M.Ω)
    refine ⟨integralClosure ℤ M.Ω, inferInstance, hded, hfin, inferInstance, hinj, hcst, ?_⟩
    intro p hp m _ hpm O _ _ _ _ _ _ _
    have hp' : (p : ℕ) ∈ S ∧ (p : ℕ) ∉ S₀ := Finset.mem_sdiff.1 (Finset.mem_preimage.1 hp)
    obtain ⟨hHT, h2, hd⟩ := hloc p hp'.1 hp'.2
    obtain ⟨_, _, _, e₀, e, _, hrl, _, _⟩ := id hTL
    refine ⟨?_, ?_⟩
    · exact hM3 E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl S₀ R.pairs hTL p hp'.1 hp'.2 hHT h2 hd (φ p) (hφ p hp'.1 hp'.2) (integralClosure ℤ M.Ω) m hpm O
    · intro τ
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hmod := (_root_.GlobalTheory.CompanionTheory.Ar.Num.pl_model M.K M.ι M.Ω M.y (integralClosure ℤ M.Ω) hinj hcst _ M.arith m O).2.1
      exact _root_.GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt hseg O ϖ hϖ M.K M.ι _ _ hmod _ _ fun W hW =>
        hTriv E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl R.pairs.x' e hrl p hp'.1 hHT (integralClosure ℤ M.Ω) m hpm O τ W hW

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem hodgeAt_stable : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH R g N ℓ t HL h1 h
  obtain ⟨⟨-, -, hX⟩, hmap, -⟩ := h
  have key : ∀ (c : 𝓞 E) (i : Fin N), ρH c (t i) ∈ HL := by
    intro c i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, ← (RingOfIntegers.basis E).sum_repr c, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _
  have stable : ∀ a, ∀ y ∈ HL, ρH a y ∈ HL := by
    intro a y hy
    rw [hX] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact key _ _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e : ρH a (r • x) = r • ρH a x := map_smul (ρH a) (r : Ω) x
      rw [e]
      exact HL.smul_mem r hx
  refine ⟨fun i => ?_, stable, fun a i => ?_⟩
  · simpa using key 1 i
  · have hi : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) :=
      hmap ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hi
    rw [← hmap]
    refine ⟨ρH a y, stable a y hy, ?_⟩
    have e' : y.1 = ℓ i := e
    change (ρH a y).1 = _
    rw [h1, e']

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArithVar_of_block_algebraic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ), IsBlockMap κ v → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsArithVar (mCoordIdeal (y ∘ v)) d → (∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) → IsArithVar (mCoordIdeal y) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | exact GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image <;> assumption)
end

