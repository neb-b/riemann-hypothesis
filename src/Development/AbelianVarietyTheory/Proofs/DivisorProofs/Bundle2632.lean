module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExistStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists : ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X → ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  first | (exact @GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (exact GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (intros; apply GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | (exact @GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (exact GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (intros; apply GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieInj

open GlobalTheory.CechDR

variable {R : Type} [CommRing R]

theorem cmpForm_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) :
    Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  intro ω
  obtain ⟨-, hinj, -⟩ := (hH R A g hab hdim).2.2.2.2.1
  haveI := hab.smooth
  haveI := hab.proper
  have hb := (cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance
    inferInstance).1
  obtain ⟨c, hc⟩ := hb.2 (clForm _ ω)
  have hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by
    rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0 := by rw [hc]; exact hmem
  rw [structureSheaf_comparison_comm] at h0
  have h1 : toH1O _ c = 0 := GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)
  have h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := h1
  rw [hodgeFiltration_eq_range] at h2
  obtain ⟨f, rfl⟩ := h2
  refine ⟨f, hinj ?_⟩
  change clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω
  rw [← comparison_formClass, hc]

section Lie

open ReciprocityTheory.ChartRestriction.G MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem lie_finite_projective (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hdim : SmoothOfRelativeDimension g A.hom) (a : OAct ℤ A) :
    Module.Finite R (GlobalTheory.Serre.Lie a) ∧ Module.Projective R (GlobalTheory.Serre.Lie a) ∧
      ∀ p, Module.rankAtStalk (R := R) (GlobalTheory.Serre.Lie a) p = g := by
  haveI : Smooth A.hom := hdim.smooth
  refine GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a
    (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end Lie

def valMap (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) :
    GlobalTheory.Serre.Lie a →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ by
    rw [LinearMap.add_apply, ← tanVal_mul v.isTangent w.isTangent, GlobalTheory.Serre.Lie.hom_add]
  map_smul' r v := LinearMap.ext fun f ↦ by
    rw [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, ← tanVal_epsScale, GlobalTheory.Serre.Lie.hom_smul]

theorem valMap_mem (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) (u : GlobalTheory.Serre.Lie a) :
    valMap A a u ∈ (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro f hf
  exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf

theorem valMap_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) [IsCommMonObj A] (a : OAct ℤ A) :
    Function.Surjective ((valMap A a).codRestrict _ (valMap_mem A a)) := by
  have hex := GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim
  have key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))),
      (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ := by
    intro φ hφ
    obtain ⟨u, hu, hu'⟩ := hex φ hφ
    exact ⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩
  intro ψ
  have hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0 := fun f hf ↦
    (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)
  exact (key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu

theorem tangent_eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w →
        (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  intro hP hH R _ A _ g hab hdim v w hv hw hvw
  haveI : IsCommMonObj A := hab.comm
  have hT := lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)
  haveI := hT.1
  haveI := hT.2.1
  have hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  have hG := (hH R A g hab hdim).2.2.1
  haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1
  haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1
  have e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R]
      GlobForm (A.hom ≫ 𝟙 (Sp R)) :=
    ((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective
      (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)
  have eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R]
      Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R))) :=
    (Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap
  haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Finite.equiv eN.symm
  haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Projective.of_equiv eN.symm
  have hbij := Module.bijective_of_surjective_of_rankAtStalk_eq
    (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by
      rw [hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]
      exact (hG.2.2 _).symm
  have h := hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv)
    (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))
  exact congrArg GlobalTheory.Serre.Lie.hom h

end GlobalTheory.LieInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem unobDim_of_formSt : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  intro hF hP hA R _ I hI R₀ _ π hπ hk A₀ _ g hab hsm
  obtain ⟨X, i, hpb, hsmX⟩ := _root_.GlobalTheory.Obs.exists_smooth_lift_of_abelian hF hP R R₀ I hI π hπ hk A₀ g hab hsm
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
  have h1 : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ A₀.hom = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀)
  obtain ⟨e, he, he'⟩ := GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb hsmX _ h1
  have P := IsPullback.of_hasPullback X.hom X.hom
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    simp only [Category.assoc, hpb.w]
    rw [← Category.assoc, ← Category.assoc, Over.w (fst A₀ A₀), Over.w (snd A₀ A₀)]
  let l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left := P.lift _ _ w
  have l1 : l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := P.lift_fst _ _ w
  have l2 : l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := P.lift_snd _ _ w
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.Obs.mul_lifts hF hA R R₀ I hI π hπ hk A₀ g hab hsm X i hpb hsmX e he he' l l1 l2
  obtain ⟨G, hG, hab'⟩ := GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hab X i hpb hsmX e he he'
    l l1 l2 m hm
  exact ⟨X, G, i, hG, hab'⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.DimLe

section

attribute [local instance low] specializationOrder

theorem topologicalKrullDim_le_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY]
  refine Order.krullDim_le_of_strictMono (f : X → Y) fun a b hab => ?_
  have h1 : f b ⤳ f a := Specializes.map hab.le f.continuous
  refine lt_of_le_of_ne h1 fun e => hab.ne ?_
  exact ((GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y X f inferInstance (f a)).2 b a
    e.symm rfl hab.le).symm

theorem topologicalKrullDim_le_of_surjective_of_isClosedMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hs : Function.Surjective f) (hc : IsClosedMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hs y
  have h : Order.height (f x) ≤ Order.height x :=
    ENat.forall_natCast_le_iff_le.mp fun n hn =>
      GlobalTheory.GenFibreDim.le_height_of_specializingMap hc.specializingMap n x hn
  exact (WithBot.coe_le_coe.mpr h).trans (Order.height_le_krullDim x)

end

theorem dim_le : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  intro K _ A B f
  have hA := _root_.GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A
  have hB := _root_.GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h := topologicalKrullDim_le_of_isFinite f.hom.left
    rw [hA, hB] at h
    exact_mod_cast h
  · have := A.ab.proper
    have := B.ab.proper
    have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
    have : UniversallyClosed (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed f.hom.left := UniversallyClosed.of_comp_of_isSeparated f.hom.left B.X.hom
    have h := topologicalKrullDim_le_of_surjective_of_isClosedMap f.hom.left
      hf.surj f.hom.left.isClosedMap
    rw [hA, hB] at h
    exact_mod_cast h

end GlobalTheory.AV.DimLe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersectiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  first | exact @GlobalTheory.AV.AbVar.inter_cls_eq_interNum | exact GlobalTheory.AV.AbVar.inter_cls_eq_interNum | (intros; apply GlobalTheory.AV.AbVar.inter_cls_eq_interNum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_swap_of_comm {K : Type} [Field K] {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  rw [AbVar.lam, AbVar.lam, mul_comm x y]
  abel

noncomputable section

def lamLeftMonoidHom {K : Type} [Field K] (A : AbVar K) (c : Pic A.X.left) {Y : Over (Sp K)} (y : Y ⟶ A.X) :
    (Y ⟶ A.X) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (AbVar.lam c x y)) (fun x x' => by
    rw [← ofAdd_add, lam_mul_left_of_cube])

theorem lam_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  intro K _ A c Y x y y' n
  have hL : ∀ x z : Y ⟶ A.X, ∀ m : ℤ, AbVar.lam c (x ^ m) z = m • AbVar.lam c x z := fun x z m => by
    have := map_zpow (lamLeftMonoidHom A c z) x m
    simpa [lamLeftMonoidHom] using congrArg Multiplicative.toAdd this
  have h1 : ∀ z : Y ⟶ A.X, AbVar.lam c 1 z = 0 := fun z => by
    simpa using hL 1 z 0
  refine ⟨?_, h1 y, ?_, hL x y n, ?_⟩
  · rw [lam_swap_of_comm c x, lam_swap_of_comm c x, lam_swap_of_comm c x, lam_mul_left_of_cube]
  · rw [lam_swap_of_comm]; exact h1 x
  · rw [lam_swap_of_comm, hL, lam_swap_of_comm]

end

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  first | (exact @GlobalTheory.AV.lam_symm_nat_add) | (exact GlobalTheory.AV.lam_symm_nat_add) | (intros; apply GlobalTheory.AV.lam_symm_nat_add  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := _root_.GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback K L σ A _ _ _ hpb
  have hB := @_root_.GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @_root_.GlobalTheory.AbCoh.finrank_HO1_descend_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @_root_.GlobalTheory.AbCoh.noPrimO2_axesO1_descend K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @_root_.GlobalTheory.AbCoh.wedgeO_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFinsumIntegralWeightSubLe
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem abs_integral_weight_sub_le_one {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (B β w : Y → ℝ) (C : ℝ) (hB : Integrable B μ) (hβ : Integrable β μ) (hle : ∀ y, B y ≤ β y)
    (hw : Measurable w) (hC : ∀ y, |w y| ≤ C) :
    |∫ y, w y * B y ∂μ - ∫ y, w y * β y ∂μ| ≤ C * (∫ y, β y ∂μ - ∫ y, B y ∂μ) := by
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ C := Eventually.of_forall fun y => by simpa using hC y
  have h1 : Integrable (fun y => w y * B y) μ := hB.bdd_mul hwm hb
  have h2 : Integrable (fun y => w y * β y) μ := hβ.bdd_mul hwm hb
  rw [← integral_sub h1 h2, ← integral_sub hβ hB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono (h1.sub h2).abs ((hβ.sub hB).const_mul C) fun y => ?_
  have h3 : 0 ≤ β y - B y := sub_nonneg.2 (hle y)
  show |w y * B y - w y * β y| ≤ C * (β y - B y)
  rw [← mul_sub, abs_mul, abs_sub_comm, abs_of_nonneg h3]
  exact mul_le_mul_of_nonneg_right (hC y) h3

theorem abs_finsum_integral_weight_sub_le :
    ∀ (S : Type) [Finite S] (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (μ : ∀ σ, Measure (Y σ)) (B β w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Integrable (B σ) (μ σ)) → (∀ σ, Integrable (β σ) (μ σ)) → (∀ σ y, B σ y ≤ β σ y) → (∀ σ, Measurable (w σ)) → 0 ≤ C → (∀ σ y, |w σ y| ≤ C) → |∑ᶠ σ, ∫ y, w σ y * B σ y ∂μ σ - ∑ᶠ σ, ∫ y, w σ y * β σ y ∂μ σ| ≤ C * (∑ᶠ σ, ∫ y, β σ y ∂μ σ - ∑ᶠ σ, ∫ y, B σ y ∂μ σ) := by
  intro S _ Y _ μ B β w C hB hβ hle hw _ hC
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  exact abs_integral_weight_sub_le_one (μ σ) (B σ) (β σ) (w σ) C (hB σ) (hβ σ) (hle σ) (hw σ) (hC σ)

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrable
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntGenSmooth

open Set

theorem archIntegrable : Published.Principalisation → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hP k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', ρ, _, hcov, hgs⟩ := GlobalTheory.GenSmoothCover.exists_isCov_genSmooth hP k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hcov.2.1 ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := GlobalTheory.T.logNorm_rationalSection_archIntegrable hcov.1 hgs (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy =>
    GlobalTheory.ArchIntAlter.mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy =>
    GlobalTheory.ArchIntAlter.logNorm_pull M ρ hη hr hy
  exact _root_.GlobalTheory.ChernDescend.chernIntegrableOn_descend k Y q e hY Y' ρ hcov.1 hcov.2.1 hcov.2.2 N σ _ _
    (GlobalTheory.ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntGenSmooth
end
end

