module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor

namespace GlobalTheory

namespace GaloisDescentNoetherian

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) :=
  ((_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).2.2 _ _ (pullback.fst T.hom π) (act hc T) (pullback.snd T.hom π) T.hom
    (act_snd hc T) pullback.condition.symm).2 (IsPullback.of_hasPullback T.hom π).flip (act_fst hc T)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g :=
  ((_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).1 Z (π ≫ g) fun a ↦ by rw [← Category.assoc, hc.inv]).unique h rfl

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  refine Over.OverMorphism.ext (cover_ext (isGaloisCover_act hc T) ?_)
  rw [← up_left H, ← up_left H, e]

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  exact ⟨fun h a ↦ congrArg (fun z ↦ z.left) (h a), fun h a ↦ Over.OverMorphism.ext (h a)⟩

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hc' := isGaloisCover_act hc T
  obtain ⟨z, hz, -⟩ := (_root_.GlobalTheory.ZM.galoisCover_descent _ _ _ Ga _ hc').1 _ (w.left ≫ φ) fun a ↦ by
    rw [← Category.assoc, (mem_equivariant hc hν).mp hw a, Category.assoc, hφ]
  refine ⟨Over.homMk z (cover_ext hc' ?_), QuotientDescent.hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := (mem_equivariant hc hν).mpr fun a ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  have h₁ := act_fst hc T a
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hφ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, e, act_snd, reassoc_of% e]

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have inj {T : Over Y} {x y : T ⟶ G'} (e : up H x = up H y) : x = y := up_injective hc H e
  have mem {T : Over Y} (z : T ⟶ G') := up_mem hc H hν hφ z
  obtain ⟨m, hm⟩ := exists_up hc H hν hφ (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := exists_up hc H hν hφ (T := 𝟙_ _) (one_mem _)
  obtain ⟨i, hi⟩ := exists_up hc H hν hφ (inv_mem (mem (𝟙 G')))
  have hm' {T : Over Y} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over Y} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over Y} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have hcomm : IsCommMonObj G' := ⟨inj (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, hcomm, H, fun T x y x₀ y₀ hx hy ↦ ?_⟩
  obtain ⟨s, hs⟩ := sec (T := T)
  have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
    rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
  rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
    QuotientDescent.hom_ext H ((k y₀).trans hy)]

end GaloisDescentNoetherian

open GaloisDescentNoetherian

theorem abelianScheme_descends_galoisCover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ _ X Y π sY Ga _ ρ G _ ν hc hq hG hν h1 hmul
  have := hc.finite
  have hinv (a : Ga) : ν a ≫ G.hom ≫ π = G.hom ≫ π := by
    rw [← Category.assoc, (hν a).1.w, Category.assoc, hc.inv]
  obtain ⟨Z, φ, sZ, -, hφ, -⟩ := _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian K G.left (G.hom ≫ π ≫ sY) Ga ν hq h1 hmul
    (fun a ↦ by rw [reassoc_of% (hinv a)]) (fun k _ _ y a hy ↦ by
      refine (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique ?_ ?_
      · rw [Category.assoc, ← (hν a).1.w, reassoc_of% hy]
      · rw [hc.one, Category.comp_id])
  obtain ⟨v, hv, -⟩ := (_root_.GlobalTheory.ZM.galoisCover_descent _ _ φ Ga ν hφ).1 Y (G.hom ≫ π) hinv
  have H : IsPullback φ G.hom (Over.mk v).hom π :=
    (((_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).2.2 _ _ φ ν G.hom v (fun a ↦ (hν a).1.w) hv.symm).1 hφ).flip
  have := hG.comm
  obtain ⟨inst, hcomm, hp⟩ := exists_grpObj (G' := Over.mk v) hc H hν hφ.inv
  refine ⟨Over.mk v, inst, φ, ?_, hp, hφ⟩
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have := hφ.fin
  have := hφ.onto
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) π :=
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩
  have hs : Smooth (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hQ ‹_›
  have hu : UniversallyClosed (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.flip hQ inferInstance
  have hsep : IsSeparated (Over.mk v).hom := by
    have : IsSeparated (φ ≫ (Over.mk v).hom) := by rw [H.w]; infer_instance
    exact SemiAbelianDescent.isSeparated_of_comp φ _
  exact ⟨hcomm, hs, ⟨⟩, SemiAbelianDescent.geometricallyConnected_of_isPullback H⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftAlongThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

theorem isUnit_of_isUnit_appTop_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (a : Γ(Y, ⊤)) (h : IsUnit (f.appTop a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ X.basicOpen (f.appTop a) := by
    rw [Scheme.basicOpen_of_isUnit _ h]; trivial
  rw [← Scheme.preimage_basicOpen_top] at hx
  exact (Y.mem_basicOpen _ _ (by trivial)).1 hx

theorem units_lift_of_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left →
      Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  intro S A _ hA T₂ T₀ k _ _ _ u
  have hb₀ : Function.Bijective (snd A T₀).left.appTop.hom :=
    CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA (IsPullback.of_hasPullback A.hom T₀.hom)
  have hk : Function.Surjective k.left.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine k.left).2
  have hc : (A ◁ k).left ≫ (snd A T₂).left = (snd A T₀).left ≫ k.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hc' : ∀ w, (A ◁ k).left.appTop ((snd A T₂).left.appTop w) =
      (snd A T₀).left.appTop (k.left.appTop w) := by
    intro w
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hc]
  obtain ⟨v, hv⟩ := hb₀.2 (u : Γ((A ⊗ T₀).left, ⊤))
  obtain ⟨w, rfl⟩ := hk v
  let e := RingEquiv.ofBijective (snd A T₀).left.appTop.hom hb₀
  have hvu : IsUnit (k.left.appTop w) := by
    have : IsUnit (e (k.left.appTop w)) := by
      show IsUnit ((snd A T₀).left.appTop (k.left.appTop w)); rw [hv]; exact u.isUnit
    exact (isUnit_map_iff e _).1 this
  have hw : IsUnit w := isUnit_of_isUnit_appTop_of_surjective k.left w hvu
  obtain ⟨w', hw'⟩ := hw.map (snd A T₂).left.appTop.hom
  refine ⟨w', Units.ext ?_⟩
  show (A ◁ k).left.appTop (w' : Γ((A ⊗ T₂).left, ⊤)) = u
  rw [hw', hc', hv]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCover

theorem cover : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  classical
  intro K _ _ A _ hA V hV
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let O : (𝟙_ (Over (Sp K)) ⟶ A) → A.left.Opens := fun a =>
    (𝟙 A * (toUnit A ≫ a)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a)⁻¹).left ⁻¹ᵁ V
  have key : ∀ y : 𝟙_ (Over (Sp K)) ⟶ A, ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, ∀ p, y.left p ∈ O a := by
    intro y
    have := GlobalTheory.AbelianProjective.isIso_transl_left y
    have : IsIso ((toUnit A ≫ y) * 𝟙 A).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit A ≫ y) * 𝟙 A)))
    have : IsIso (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A))))
    have h1 : ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h2 : (((ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h3 := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) h1 h2
    obtain ⟨a, ha⟩ := GlobalTheory.AbelianProjective.exists_point A
      ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V ⊓ (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V).isOpen).isLocallyClosed h3
    refine ⟨a, fun p => ?_⟩
    have e : y ≫ (𝟙 A * (toUnit A ≫ a)) = a ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have e' : y ≫ (𝟙 A * (toUnit A ≫ a)⁻¹) = a ≫ ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
      rfl
    have hp := ha p
    refine ⟨?_, ?_⟩
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)).left) p ∈ V
      rw [← Over.comp_left, e, Over.comp_left]
      exact hp.1
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)⁻¹).left) p ∈ V
      rw [← Over.comp_left, e', Over.comp_left]
      exact hp.2
  have htop : ⨆ a, O a = ⊤ := by
    by_contra hne
    have hc : ((⨆ a, O a : A.left.Opens) : Set A.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := GlobalTheory.AbelianProjective.exists_point A
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨a, ha⟩ := key y
    exact hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha _⟩)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun a => (O a : Set A.left))
    (fun a => (O a).isOpen) fun x _ => by
      have hx : x ∈ ⨆ a, O a := by rw [htop]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, top_unique fun x _ => ?_⟩
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨F.equivFin ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]; exact hx⟩

end GlobalTheory.AbCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FamCalc

variable {S : Scheme.{0}} {A : Over S}

theorem whisker_eq {Y T : Over S} (y : Y ⟶ T) : A ◁ y = lift (fst A Y) (snd A Y ≫ y) := by
  ext <;> simp

theorem lift_whisker {Y T Z : Over S} (y : Y ⟶ T) (a : Z ⟶ A) (t : Z ⟶ Y) :
    lift a t ≫ A ◁ y = lift a (t ≫ y) := by
  ext <;> simp

theorem pull_whisker_evc {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) (a : Z ⟶ A)
    (t : Z ⟶ Y) :
    CechPic.pull (lift a t).left (CechPic.pull (A ◁ y).left (cls N hN)) = evc hN a (t ≫ y) := by
  rw [← pull_comp, ← Over.comp_left, lift_whisker, evc]

theorem evc_whisker {T Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = CechPic.pull (A ◁ y).left (cls N hN) := by
  rw [evc, whisker_eq]

theorem evc_ev_whisker {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T)
    (h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB) (a : Z ⟶ A) (t : Z ⟶ Y) :
    evc h a t = evc hN a (t ≫ y) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem famCalc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  intro S A _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Y N y hN
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
    refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
    simp only [evc_ev_whisker hN.isLB y h]
    exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
  · intro T U Y N M hN hM y u D hD hc
    refine ⟨hD, (isAdditive_iff hD).2 fun Z a a' t ↦ ?_⟩
    have aN := (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
    have aM := (isAdditive_iff hM.isLB).1 hM.add Z a a' (t ≫ u)
    rcases hc with hc | hc
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) + evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_add (f := _), pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) - evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_sub, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
  · intro T U Y N M hN hM y u
    rw [same_iff hN hM, evc_whisker, evc_whisker]
  · intro T U Y Z N M y u z hN hM h
    rw [same_iff hN hM] at h ⊢
    have e := congrArg (CechPic.pull (A ◁ z).left) h
    rwa [pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc] at e
  · intro T U Y Z N M y z u hN hM
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN _
    rw [same_iff h hM, same_iff hN hM, evc_ev_whisker hN y h, Category.assoc]

end GlobalTheory.FamCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineMilnorSquareOfCartesianRingSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem milnor_of_ring_square : ∀ (P C₁ C₂ C₀ : Type) [CommRing P] [CommRing C₁] [CommRing C₂] [CommRing C₀] (p₁ : P →+* C₁) (p₂ : P →+* C₂) (q₁ : C₁ →+* C₀) (q₂ : C₂ →+* C₀), q₁.comp p₁ = q₂.comp p₂ → (∀ x, p₁ x = 0 → p₂ x = 0 → x = 0) → (∀ a b, q₁ a = q₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) → Function.Surjective q₂ → Milnor (spMap p₁) (spMap p₂) (spMap q₁) (spMap q₂) := by
  intro P C₁ C₂ C₀ _ _ _ _ p₁ p₂ q₁ q₂ hw hinj hsurj hq₂
  have hwc : CommRingCat.ofHom p₁ ≫ CommRingCat.ofHom q₁ = CommRingCat.ofHom p₂ ≫ CommRingCat.ofHom q₂ := by
    ext x; exact congrArg (fun f : P →+* C₀ => f x) hw
  have H : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom q₁) (CommRingCat.ofHom q₂) := by
    refine IsPullback.of_map (forget CommRingCat) hwc ?_
    rw [Types.isPullback_iff]
    refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hwc], ?_, ?_⟩
    · rintro x y ⟨h1, h2⟩
      have h1' : p₁ x = p₁ y := h1
      have h2' : p₂ x = p₂ y := h2
      exact sub_eq_zero.mp (hinj _ (by rw [map_sub, h1', sub_self]) (by rw [map_sub, h2', sub_self]))
    · intro a b hab
      exact hsurj a b hab
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective _ hq₂, ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, hwc]
  · refine IsPullback.of_iso H (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso _).symm ?_ ?_ ?_ ?_ <;>
    simp [spMap, Scheme.ΓSpecIso_inv_naturality]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolarStatement
section
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → ∀ z z' : Fin 8 → X₀, (∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z = qW W β (y + z') - qW W β y - qW W β z') → z' = fun a => ∑ b, E' a b • z b := by
  first | exact @GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | exact GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | (intros; apply GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar <;> assumption)
end

