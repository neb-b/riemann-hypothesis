module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAevalRatiosLe
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneBlockEq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdNotMemPrimeOfForall
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RatioMonHomog
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsAmpleBaseLocalizationEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0046
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.A28
section
namespace PositivityTheory.HtPt.Ktw

theorem a21 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurves.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurves.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurvesDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurvesLift.proof

theorem a22 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenTransfer.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenTransfer.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ChartKernel.proof

theorem a23 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelPoint.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelPoint.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenOfModel.proof a22
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelOfBlockGen.proof

theorem a24 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RealiseRestrict.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RealiseRestrict.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ResidueMap.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ResidueGen.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RestrictGen.proof

theorem a25 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveNumModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveNumModel.proof a23 a24 a5 a18 a21

theorem a26 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurveNum.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurveNum.proof a25

theorem a27 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeNef.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeNef.proof a21 a26

theorem a28 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SegreRealise.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefB.segreRealise a20 a27 a18

theorem a65 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelNefEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelNefEq.proof a20 a27

theorem a66 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PowRealises.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PowRealises.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof

theorem a67 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelMulSecs.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelMulSecs.of_powRealises a66

theorem a68 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ChartSecGen.full

theorem a69 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeGen.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeGen.proof a68

theorem a70 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeVeryAmple.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeVeryAmple.proof a69

theorem a71 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelVeryAmpleEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelVeryAmpleEq.proof
    PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a67 a70

theorem a74 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
    PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69

end PositivityTheory.HtPt.Ktw
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelGeo
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PositivityTheory.HtPt.Gh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {A R : Type} [CommRing A] [CommRing R]
    (φ : A →+* R) (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      ∀ (n : ℕ) (b : Module.Basis (Fin n) A E), ∃ b' : Module.Basis (Fin n) R F, ∀ i, b' i = j (b i) := by
  have h_alg : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h_fst : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
    rw [spec_comp, spec_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [GlobalTheory.CompanionTheory.Ar.dualMap]
  have h_eps (a : A) : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul a)) =
      Spec.map (CommRingCat.ofHom (epsMul (φ a))) ≫ Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) := by
    rw [spec_comp, spec_comp]
    congr 2
    refine RingHom.ext fun b => ?_
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]
  let base : epsAt z ⟶ epsAt x := Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ))) (by
    change _ ≫ _ ≫ x = _ ≫ z
    rw [← Category.assoc, h_alg, Category.assoc, hz])
  have hbase (a : A) : base ≫ epsScale x a = epsScale z (φ a) ≫ base :=
    Over.OverMorphism.ext (h_eps a)
  have ht (e : E) : IsTanAt G z (base ≫ M.pt e) := by
    change _ ≫ Spec.map _ ≫ (M.pt e).left = _
    rw [← Category.assoc, h_fst, Category.assoc, M.tan e]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom φ)) hz : Over.mk z ⟶ Over.mk x))
  choose j hj using fun (e : E) => N.onto _ (ht e)
  have hadd : ∀ e e', j (e + e') = j e + j e' := fun e e' => N.inj (by
    rw [hj, N.add, hj, hj, M.add, MonObj.comp_mul])
  have hsm : ∀ (a : A) e, j (a • e) = φ a • j e := fun a e => N.inj (by
    rw [hj, N.pt_smul, M.pt_smul, hj, ← Category.assoc, hbase, Category.assoc])
  have hl : ∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left :=
    fun e => congrArg CommaMorphism.left (hj e)
  refine ⟨AddMonoidHom.mk' j hadd, hl, hsm, fun n b => ?_⟩
  subst hz
  letI := φ.toAlgebra
  letI : Module A F := Module.compHom F φ
  haveI : IsScalarTower A R F := ⟨fun a r y => mul_smul (φ a) r y⟩
  let jL : E →ₗ[A] F := { toFun := j, map_add' := hadd, map_smul' := hsm }
  have hb : IsBaseChange R jL := PositivityTheory.HtPt.Htat.Lie.isBaseChange_lie x M R F N jL hl
  exact ⟨hb.basis b, fun i => hb.basis_apply b i⟩

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_frame [IsCommMonObj G] [Smooth G.hom] (M : LieModel G ξ E) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C] {EC : Type} [AddCommGroup EC] [Module C EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) (h : genPt ξ ⤳ centre z)
    (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) :
    ∃ (n : ℕ) (β : Module.Basis (Fin n) Ω E) (gm : Module.Basis (Fin n) C EC),
      (∀ i, β i ∈ M.lat ⟨centre z, h⟩) ∧
      ∀ e x, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x) ↔
        ∃ c : Fin n → X.presheaf.stalk (centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)),
          e = ∑ i, genMap ξ ⟨_, h'⟩ (c i) • β i ∧
          x = ∑ i, (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom (c i) • gm i := by
  have hsp := centre_specializes (algebraMap R C) z
  generalize hzC : Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z = zC at *
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨EB, _, _, ⟨MB⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre zC)) (X.fromSpecStalk (centre zC))
  obtain ⟨hfin, hproj, -⟩ := PositivityTheory.HtPt.Htat.lie_proj X G _ _ EA MA
  haveI : Module.Free (X.presheaf.stalk (centre z)) EA := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis (X.presheaf.stalk (centre z)) EA
  obtain ⟨k, hk, -, hkb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (R := X.presheaf.stalk (centre zC))
    (X.presheaf.stalkSpecializes hsp).hom _ _ (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp) MA MB
  obtain ⟨i, hi, his, hib⟩ := exists_base (A := X.presheaf.stalk (centre zC)) (genMap ξ ⟨centre zC, h'⟩) _ ξ (spec_genMap ξ ⟨centre zC, h'⟩) MB M
  obtain ⟨j, hj, hjs, hjb⟩ := exists_base (A := X.presheaf.stalk (centre zC)) (R := C)
    (Scheme.stalkClosedPointTo zC).hom _ zC
    (spec_centre zC) MB MC
  obtain ⟨b', hb'⟩ := hkb _ b
  obtain ⟨β, hβ⟩ := hib _ b'
  obtain ⟨gm, hgm⟩ := hjb _ b'
  have hsum : ∀ c : Fin _ → X.presheaf.stalk (centre zC), i (∑ l, c l • b' l) = ∑ l, genMap ξ ⟨_, h'⟩ (c l) • β l ∧
      j (∑ l, c l • b' l) = ∑ l, (Scheme.stalkClosedPointTo zC).hom (c l) • gm l := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    exact ⟨Finset.sum_congr rfl fun l _ => by rw [hβ]; exact his _ _,
      Finset.sum_congr rfl fun l _ => by rw [hgm]; exact hjs _ _⟩
  refine ⟨_, β, gm, fun l => (M.mem_lat_iff _ _).2 ⟨MA.pt (b l), MA.tan _, ?_⟩, fun e x => ⟨?_, ?_⟩⟩
  · rw [hβ, hb', hi, hk, ← Category.assoc, spec_comp, dualMap_comp]
    congr 4
    exact RingHom.ext fun s => genMap_specializes ⟨centre z, h⟩ h' hsp s
  · rintro ⟨_, v, hv, hx⟩
    obtain ⟨a, rfl⟩ := MB.onto v hv.1
    have h1 : e = i a := M.inj (Over.OverMorphism.ext (hv.2.trans (hi a).symm))
    have h2 : x = j a := MC.inj (Over.OverMorphism.ext (hx.trans (hj a).symm))
    refine ⟨b'.repr a, ?_, ?_⟩
    · rw [← (hsum _).1, b'.sum_repr, h1]
    · rw [← (hsum _).2, b'.sum_repr, h2]
  · rintro ⟨c, rfl, rfl⟩
    rw [← (hsum c).1, ← (hsum c).2]
    exact ⟨h', MB.pt _, ⟨MB.tan _, hi _⟩, hj _⟩

theorem valAt_act (M : LieModel G ξ E) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {F : Type} [AddCommGroup F] [Module R F] (N : LieModel G z F) (f : G ⟶ G) [IsMonHom f] (T : E →ₗ[Ω] E)
    (T' : F →ₗ[R] F) (hT : M.IsDiffOf f T) (hT' : N.IsDiffOf f T') {e : E} {x : F} (h : M.ValAt z e (N.pt x)) :
    M.ValAt z (T e) (N.pt (T' x)) := by
  obtain ⟨h, v, ⟨h1, h2⟩, h3⟩ := h
  refine ⟨h, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · unfold IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  · rw [hT e, Over.comp_left, Over.comp_left, h2]
    exact Category.assoc _ _ _
  · rw [hT' x, Over.comp_left, Over.comp_left, h3]
    exact Category.assoc _ _ _

theorem unitAt_centre_iff (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (n : ℕ) : unitAt ξ ⟨centre z, h⟩ (n : Ω) ↔ IsUnit (n : R) := by
  constructor
  · rintro ⟨h0, -, s, hs⟩
    have h1 : (n : X.presheaf.stalk (centre z)) * s = 1 := hξ.inj ⟨_, h⟩ (by
      rw [map_mul, map_one, hs, map_natCast, mul_inv_cancel₀ h0])
    have h2 := (IsUnit.of_mul_eq_one _ h1).map (Scheme.stalkClosedPointTo z).hom
    rwa [map_natCast] at h2
  · intro hu
    have h1 : IsUnit (n : X.presheaf.stalk (centre z)) :=
      (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit _ (by rwa [map_natCast])
    obtain ⟨u, hu⟩ := h1
    have e : genMap ξ ⟨centre z, h⟩ u = n := by rw [hu]; exact map_natCast _ n
    rw [← e]
    exact ⟨(u.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), map_units_inv _ u⟩⟩

end PositivityTheory.HtPt.Gh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfEx
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.HtPt.Htat.ExistsHodgeTate.exists_isHT (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hT hS L _ _ M χ
  haveI : Smooth G.hom := hS
  obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Htat.ht_char_section_of hHenselian hBaseChange hRegular) R T Γ χ
  obtain ⟨l, hl⟩ := PositivityTheory.HtPt.Htat.ht_linear R T Γ S G x N i hT L M χ s hs
  have hP := (PositivityTheory.HtPt.Htat.lie_proj S G R x L M).2.1
  obtain ⟨w, hw⟩ := Module.projective_lifting_property
    (Submodule.mkQ (Ideal.span {(N : R)})) l (Submodule.mkQ_surjective _)
  refine ⟨w, s, hs, fun e => ?_⟩
  obtain ⟨v, ⟨hv1, hv2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R T Γ S G x N i hT L M e
  refine ⟨v, hv1, hv2, ?_⟩
  rw [hl e v ⟨hv1, hv2⟩]
  have := LinearMap.congr_fun hw e
  simp only [LinearMap.comp_apply] at this
  rw [← this]
  rfl

theorem PositivityTheory.HtPt.Htat.ht_exists_of (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w :=
  @PositivityTheory.HtPt.Htat.ExistsHodgeTate.exists_isHT hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lie_fin : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  intro S G _ _ R _ x E _ _ M
  exact ⟨(lie_proj S G R x E M).1, (lie_proj S G R x E M).2.1⟩

theorem lie_bc : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) := by
  intro S G _ R R' _ _ _ x E E' _ _ _ _ M M'
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R R' (algebraMap R R') x E E' M M'
  refine ⟨j.toAddMonoidHom, fun e => ?_, fun a e => j.map_smulₛₗ a e, fun hsm n b => ?_⟩
  · have := hj e
    simp only [Category.comp_id] at this
    exact this
  · haveI : Smooth G.hom := hsm
    letI : Module R E' := Module.compHom E' (algebraMap R R')
    haveI : IsScalarTower R R' E' := ⟨fun a c v => by
      show (a • c) • v = algebraMap R R' a • c • v
      rw [Algebra.smul_def, mul_smul]⟩
    let β : E →ₗ[R] E' :=
      { toFun := j
        map_add' := j.map_add
        map_smul' := fun a e => j.map_smulₛₗ a e }
    have hb := Lie.isBaseChange_lie x M R' E' M' β (fun e => by
      have := hj e
      simp only [Category.comp_id] at this
      exact this)
    have hbk : ∀ k, hb.basis b k = j (b k) := fun k => by
      rw [IsBaseChange.basis_apply]
      rfl
    have hfun : (fun k => j.toAddMonoidHom (b k)) = ⇑(hb.basis b) := funext fun k => (hbk k).symm
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (hb.basis b).linearIndependent
    · rw [hfun]
      exact (hb.basis b).span_eq

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Htat

theorem lie_bc_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (PositivityTheory.HtPt.Htat.lie_proj S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end PositivityTheory.HtPt.Htat
end

