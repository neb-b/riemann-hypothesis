module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.geometricallyConnected_of_isPullback_of_surjective {X Y X' Y' : Scheme.{0}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun K _ t Z fst snd hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd s t).surjective (Nonempty.some inferInstance)
  let e := (pullback s t).fromSpecResidueField z
  let u := e ≫ pullback.fst s t
  let v := e ≫ pullback.snd s t
  have huv : v ≫ t = u ≫ s := by simp only [u, v, Category.assoc, pullback.condition]
  have hbig : IsPullback (pullback.fst snd v ≫ fst) (pullback.snd snd v) q (u ≫ s) :=
    huv ▸ (IsPullback.of_hasPullback snd v).paste_horiz hZ
  have hsmall := IsPullback.of_right
    (h₁₁ := h.lift (pullback.fst snd v ≫ fst) (pullback.snd snd v ≫ u)
      (by simpa only [Category.assoc] using hbig.w))
    (by simpa using hbig) (by simp) h
  have hc : ConnectedSpace ↥(pullback snd v) :=
    GeometricallyConnected.geometrically_connectedSpace u _ _ hsmall
  have hv : Surjective v := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst snd v).surjective.connectedSpace (pullback.fst snd v).continuous

theorem GlobalTheory.torusExtension_smooth_geometricallyConnected {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] (E : TorusExtension G) : Smooth E.q.left ∧ GeometricallyConnected E.q.left ∧ Smooth G.hom ∧ GeometricallyConnected G.hom ∧ IsSeparated G.hom := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_flat
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI : Smooth E.B.hom := E.isAbelian.smooth
  haveI : GeometricallyConnected E.B.hom := E.isAbelian.geomConnected
  haveI : IsProper E.B.hom := E.isAbelian.proper
  have hTc : GeometricallyConnected (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    ((GlobalTheory.splitTorus_properties (Spec (CommRingCat.of K))).1 E.X).2.2.2.2.2.2.2.1
  have hiq : E.i ≫ E.q = 1 := E.isKernel.w
  have key : ∀ {W : Over (Spec (CommRingCat.of K))} (a b : W ⟶ G), a ≫ E.q = b ≫ E.q →
      (a⁻¹ * b) ≫ E.q = toUnit W ≫ (η : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.B) := by
    intro W a b hab
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, _root_.inv_mul_cancel]
    try exact rfl
  let m : G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X ⟶ G := fst _ _ * (snd _ _ ≫ E.i)
  have hm : ∀ {W : Over (Spec (CommRingCat.of K))} (l : W ⟶ G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X),
      l ≫ m = (l ≫ fst _ _) * ((l ≫ snd _ _) ≫ E.i) := by
    intro W l
    simp only [m, MonObj.comp_mul, Category.assoc]
  have hw : fst _ _ ≫ E.q = m ≫ E.q := by
    simp only [m, MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  have hsq : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)) m E.q E.q :=
    IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
      (fun c => lift c.fst (E.isKernel.lift (c.fst⁻¹ * c.snd) (toUnit _) (key _ _ c.condition)))
      (fun c => by rw [lift_fst])
      (fun c => by rw [hm, lift_fst, lift_snd, IsPullback.lift_fst, mul_inv_cancel_left])
      (fun c l h1 h2 => by
        refine CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, h1]) ?_
        rw [lift_snd]
        refine E.isKernel.hom_ext ?_ (toUnit_unique _ _)
        rw [IsPullback.lift_fst]
        rw [hm, h1] at h2
        exact eq_inv_mul_of_mul_eq h2))
  have hsqS : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left m.left
      E.q.left E.q.left := hsq.map (Over.forget _)
  have hprod : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left
      (snd G (splitTorus (Spec (CommRingCat.of K)) E.X)).left G.hom
      (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    IsPullback.of_hasPullback _ _
  have hfs : Smooth (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hprod.flip inferInstance
  have hfc : GeometricallyConnected (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip hTc
  have hqs : Smooth E.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqS
      ⟨⟨E.q_surjective, E.q_flat⟩, E.q_quasiCompact⟩ hfs
  have hqc : GeometricallyConnected E.q.left :=
    GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hsqS.flip
  have hqa : IsAffineHom E.q.left :=
    GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel _ G E.B _ E.q E.i E.q_hom E.i_hom
      E.q_flat E.q_surjective E.q_quasiCompact E.isKernel inferInstance
  rw [← Over.w E.q]
  refine ⟨hqs, hqc, inferInstance, GeometricallyConnected.comp _ _, inferInstance⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GroupRingHomConstOfLaurent
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupRingConst

noncomputable def pt {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) : AddMonoidAlgebra R X →+* F :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom F).comp c) (fun _ _ ↦ Commute.all _ _)

@[simp] lemma pt_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (a : X) (x : R) :
    pt r c (AddMonoidAlgebra.single a x) = r x * (c (Multiplicative.ofAdd a) : F) := by
  simp [pt, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma pt_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) :
    (pt r c).comp (algebraMap R (AddMonoidAlgebra R X)) = r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, pt_single]

def powChar {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G) :
    Multiplicative X →* G :=
  (zpowersHom G u).comp (AddMonoidHom.toMultiplicative l)

@[simp] lemma powChar_apply {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G)
    (a : X) : powChar l u (Multiplicative.ofAdd a) = u ^ l a := by
  simp [powChar]

lemma eq_prod_powChar {G X I : Type} [CommGroup G] [AddCommGroup X] [Fintype I]
    (b : Module.Basis I ℤ X) (c : Multiplicative X →* G) :
    c = ∏ i, powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i))) := by
  refine MonoidHom.ext fun m => ?_
  obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = m := ⟨Multiplicative.toAdd m, rfl⟩
  rw [MonoidHom.finsetProd_apply]
  simp only [powChar_apply]
  conv_lhs => rw [← b.sum_repr a]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  simp [Module.Basis.coord_apply]

noncomputable def family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) : AddMonoidAlgebra R X →+* AddMonoidAlgebra F ℤ :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap F (AddMonoidAlgebra F ℤ)).comp r)
    (((algebraMap F (AddMonoidAlgebra F ℤ)).toMonoidHom.comp ((Units.coeHom F).comp c)) *
      ((AddMonoidAlgebra.of F ℤ).comp (AddMonoidHom.toMultiplicative l)))
    (fun _ _ ↦ Commute.all _ _)

lemma family_single {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (a : X) (x : R) :
    family r c l (AddMonoidAlgebra.single a x) =
      AddMonoidAlgebra.single (l a) (r x * (c (Multiplicative.ofAdd a) : F)) := by
  simp [family, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single,
    AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.of_apply, _root_.mul_assoc]

lemma family_comp_algebraMap {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) :
    (family r c l).comp (algebraMap R (AddMonoidAlgebra R X)) =
      (algebraMap F (AddMonoidAlgebra F ℤ)).comp r := by
  ext x
  simp [AddMonoidAlgebra.coe_algebraMap, family_single]

lemma pt_comp_family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (u : Fˣ) :
    (pt (RingHom.id F) (zpowersHom Fˣ u)).comp (family r c l) = pt r (c * powChar l u) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;>
    (rw [RingHom.comp_apply, family_single, pt_single, pt_single]
     simp [powChar_apply])

lemma spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

private lemma powChar_one {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) :
    GlobalTheory.GroupRingConst.powChar l (1 : G) = 1 := by
  refine MonoidHom.ext fun m => ?_
  rw [MonoidHom.one_apply, ← ofAdd_toAdd m, GlobalTheory.GroupRingConst.powChar_apply, one_zpow]

private lemma pt_eq_lemma_2 {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (φ : AddMonoidAlgebra R X →+* F) :
    φ = GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X)))
      ((φ.toMonoidHom.comp (AddMonoidAlgebra.of R X)).toHomUnits) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_)
  · simp [GlobalTheory.GroupRingConst.pt_single, AddMonoidAlgebra.coe_algebraMap]
  · simp [GlobalTheory.GroupRingConst.pt_single, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, _root_.one_mul]

private lemma step_lemma_3 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s)
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) (l : X →+ ℤ) (u : Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l u))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f := by
  obtain ⟨k, hk⟩ := h L (Spec.map (CommRingCat.ofHom r) ≫ s)
    (Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.family r c l)) ≫ f) (by
      rw [Category.assoc, hf, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.family_comp_algebraMap, ← GlobalTheory.GroupRingConst.spec_comp,
        Category.assoc])
  have key : ∀ v : Lˣ, Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (c * GlobalTheory.GroupRingConst.powChar l v))) ≫ f = k := by
    intro v
    rw [← GlobalTheory.GroupRingConst.pt_comp_family, ← GlobalTheory.GroupRingConst.spec_comp, Category.assoc, hk, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp,
      GlobalTheory.GroupRingConst.pt_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h1 := key 1
  rw [powChar_one, _root_.mul_one] at h1
  rw [key u, h1]

private lemma chain_lemma_4 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (r : R →+* L) (c : Multiplicative X →* Lˣ) :
    Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r c)) ≫ f = Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ t : Finset (Module.Free.ChooseBasisIndex ℤ X),
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r (∏ i ∈ t,
        GlobalTheory.GroupRingConst.powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i)))))) ≫ f =
      Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt r 1)) ≫ f := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, _root_.mul_comm (GlobalTheory.GroupRingConst.powChar _ _), step_lemma_3 p h s f hf, ih]
  conv_lhs => rw [GlobalTheory.GroupRingConst.eq_prod_powChar b c]
  exact key Finset.univ

private lemma pts_lemma_5 {S Y : Scheme.{0}} (p : Y ⟶ S)
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    {R X : Type} [CommRing R] [AddCommGroup X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) [Module.Free ℤ X] [Module.Finite ℤ X]
    (L : Type) [Field L] (φ : AddMonoidAlgebra R X →+* L) :
    Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.GroupRingConst.pt (RingHom.id R) 1)) ≫ f := by
  rw [← Category.assoc, ← Category.assoc, GlobalTheory.GroupRingConst.spec_comp, GlobalTheory.GroupRingConst.spec_comp]
  have e1 : (φ.comp (algebraMap R (AddMonoidAlgebra R X))).comp
      (GlobalTheory.GroupRingConst.pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)) =
      GlobalTheory.GroupRingConst.pt (φ.comp (algebraMap R (AddMonoidAlgebra R X))) (1 : Multiplicative X →* Lˣ) := by
    refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;> simp [GlobalTheory.GroupRingConst.pt_single]
  rw [e1]
  conv_lhs => rw [pt_eq_lemma_2 φ]
  exact chain_lemma_4 p h s f hf L _ _

end GlobalTheory.GroupRingConst

open GlobalTheory.GroupRingConst in
theorem GlobalTheory.groupRing_hom_const_of_laurent {S Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p]
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) :
    ∃ k : Spec (CommRingCat.of R) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ k := by
  classical
  have : UniqueSums X := UniqueSums.of_injective_addHom
    (Module.Free.chooseBasis ℤ X).repr.toLinearMap.toAddMonoidHom.toAddHom
    (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  have hcomp : (pt (RingHom.id R) (1 : Multiplicative X →* Rˣ)).comp
      (algebraMap R (AddMonoidAlgebra R X)) = RingHom.id R := pt_comp_algebraMap _ _
  refine ⟨Spec.map (CommRingCat.ofHom (pt (RingHom.id R) 1)) ≫ f, ?_⟩
  refine ext_of_fromSpecResidueField_eq _ _ p Set.univ dense_univ (fun x _ => ?_) ?_
  · obtain ⟨φ, hφ⟩ : ∃ φ : AddMonoidAlgebra R X →+*
        ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).residueField x),
        Spec.map (CommRingCat.ofHom φ) = (Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x :=
      ⟨(Spec.preimage ((Spec (CommRingCat.of (AddMonoidAlgebra R X))).fromSpecResidueField x)).hom,
        by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    rw [← hφ]
    exact pts_lemma_5 p h s f hf _ φ
  · rw [hf, Category.assoc, Category.assoc, hf,
      ← Category.assoc _ (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))), spec_comp, hcomp,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing A] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := GlobalTheory.geometricallyReduced_of_smooth f
  have : _root_.IsReduced (CommRingCat.of A) := inferInstanceAs (_root_.IsReduced A)
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp inferInstance

theorem GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := Algebra.Smooth.flat A₀ B₀
  have key : _root_.IsReduced (TensorProduct A₀ B₀ A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (TensorProduct A₀ D B₀) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom)
    ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)

private theorem isReduced_of_smooth_of_isAffine_of_isReduced {Y T : Scheme.{0}} (g : Y ⟶ T) [Smooth g]
    [IsAffine T] [IsReduced T] : IsReduced Y := by
  have hι : ∀ j, Smooth (Y.affineOpenCover.f j) := fun j => inferInstance
  refine @IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)

  have h₁ : Smooth (g ≫ T.isoSpec.hom) := inferInstance
  have h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ (hι j) h₁
  have hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom))) := by
    rw [Spec.map_preimage]; exact h₂
  let := (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra
  have : Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j) := HasRingHomProperty.Spec_iff.mp hs
  have : _root_.IsReduced (Y.affineOpenCover.X j) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)
  show IsReduced (Spec (Y.affineOpenCover.X j))
  infer_instance

theorem GlobalTheory.isReduced_of_smooth_of_isReduced {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [IsReduced S] : IsReduced X := by

  have hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨V, hV⟩ : ∃ V : S.affineOpens, f x ∈ (V : S.Opens) := by
      have hx : f x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hx
    have : IsAffine (V : S.Opens) := V.2
    have hU : IsReduced (f ⁻¹ᵁ (V : S.Opens)) :=
      isReduced_of_smooth_of_isAffine_of_isReduced (f ∣_ (V : S.Opens))
    let y : (f ⁻¹ᵁ (V : S.Opens) : X.Opens) := ⟨x, hV⟩
    have := @isReduced_stalk_of_isReduced _ hU y
    exact isReduced_of_injective (Scheme.Opens.stalkIso _ y).symm.commRingCatIsoToRingEquiv
      (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X
end

