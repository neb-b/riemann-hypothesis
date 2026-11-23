module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace GaloisDescent

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := by
  unfold act
  exact pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := by
  unfold act
  exact pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) := by
  have hpb : IsPullback (pullback.snd T.hom π) (pullback.fst T.hom π) π T.hom :=
    (IsPullback.of_hasPullback T.hom π).flip
  exact ((_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).2.2 (pullback T.hom π) T.left (pullback.fst T.hom π) (act hc T)
    (pullback.snd T.hom π) T.hom (fun a => act_snd hc T a) pullback.condition.symm).2 hpb
    (fun a => act_fst hc T a)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g := by
  obtain ⟨f', -, huniq⟩ := (_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).1 Z (π ≫ f)
    (fun a => by rw [← Category.assoc, hc.inv])
  exact (huniq f rfl).trans (huniq g h.symm).symm

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  have h1 := up_left H x
  have h2 := up_left H y
  rw [e] at h1
  apply Over.OverMorphism.ext
  exact cover_ext (isGaloisCover_act hc T) (h1.symm.trans h2)

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  refine forall_congr' fun a => ?_
  change preHom _ w = pushHom _ _ w ↔ _
  rw [Over.OverMorphism.ext_iff]
  unfold preHom pushHom
  simp only [MonoidHom.mk'_apply, Over.comp_left, Over.homMk_left]
  unfold pushPt
  simp

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hinv : ∀ a, act hc T a ≫ (w.left ≫ φ) = w.left ≫ φ := fun a => by
    rw [← Category.assoc, (mem_equivariant hc hν).1 hw a, Category.assoc, hφ]
  obtain ⟨f', hf', -⟩ := (_root_.GlobalTheory.ZM.galoisCover_descent _ _ _ Ga _ (isGaloisCover_act hc T)).1 G'.left (w.left ≫ φ) hinv
  have hw' : w.left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w w
  have hbase : f' ≫ G'.hom = T.hom := by
    apply cover_ext (isGaloisCover_act hc T)
    rw [← Category.assoc, hf', Category.assoc, H.w, ← Category.assoc, hw', pullback.condition]
  refine ⟨Over.homMk f' hbase, GlobalTheory.QuotientDescent.hom_ext H ?_⟩
  rw [up_left]
  simp [hf']

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := by
  rw [mem_equivariant]
  intro a
  have hu : (up H z).left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w (up H z)
  apply H.hom_ext
  · rw [Category.assoc, Category.assoc, hφ, up_left, ← Category.assoc, act_fst]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, ← Category.assoc (up H z).left, hu]
    exact act_snd hc T a

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have hsurj : ∀ (T : Over Y) (w : equivariant hc hν T), ∃ z : T ⟶ G', up H z = w.1 :=
    fun T w => exists_up hc H hν hφ w.2
  let e : ∀ T : Over Y, (T ⟶ G') ≃ equivariant hc hν T := fun T =>
    Equiv.ofBijective (fun z => ⟨up H z, up_mem hc H hν hφ z⟩)
      ⟨fun x y h => up_injective hc H (congrArg Subtype.val h),
       fun w => (hsurj T w).imp fun z hz => Subtype.ext hz⟩
  have hmap : ∀ {T T' : Over Y} (u : T' ⟶ T) (w : equivariant hc hν T),
      (Over.pullback π).map u ≫ w.1 ∈ equivariant hc hν T' := by
    intro T T' u w
    obtain ⟨z, hz⟩ := hsurj T w
    rw [← hz, ← up_comp]
    exact up_mem hc H hν hφ (u ≫ z)
  let F : (Over Y)ᵒᵖ ⥤ CommGrpCat :=
    { obj := fun T => CommGrpCat.of (equivariant hc hν T.unop)
      map := fun {T T'} u => CommGrpCat.ofHom
        { toFun := fun w => ⟨(Over.pullback π).map u.unop ≫ w.1, hmap u.unop w⟩
          map_one' := Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_one)
          map_mul' := fun w w' => Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_mul w.1 w'.1) }
      map_id := fun T => by
        ext w
        simp
      map_comp := fun u u' => by
        ext w
        simp }
  let α : (F ⋙ forget CommGrpCat).RepresentableBy G' :=
    { homEquiv := fun {T} => e T
      homEquiv_comp := fun {T T'} u z => Subtype.ext (up_comp H u z) }
  let inst : CommGrpObj G' := CommGrpObj.ofRepresentableBy G' F α
  refine ⟨inferInstance, inferInstance, H, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hmul : up H (x₀ * y₀) = up H x₀ * up H y₀ :=
    congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy G' (F ⋙ forget₂ CommGrpCat GrpCat) α).hom.app
      (Opposite.op (Over.mk (T.hom ≫ π)))).hom.map_mul x₀ y₀)
  let s₀ : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)) :=
    Over.homMk (pullback.lift (𝟙 T.left) T.hom (by simp)) (pullback.lift_snd _ _ _)
  have hs₀ : ∀ (z : Over.mk (T.hom ≫ π) ⟶ G') (t : T ⟶ G), z.left = t.left ≫ φ → s₀ ≫ up H z = t := by
    intro z t hz
    apply GlobalTheory.QuotientDescent.hom_ext H
    rw [Over.comp_left, Category.assoc, up_left, hz]
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)
  have key : s₀ ≫ up H (x₀ * y₀) = x * y := by
    rw [hmul, ← hs₀ x₀ x hx, ← hs₀ y₀ y hy]
    exact (preHom s₀).map_mul (up H x₀) (up H y₀)
  have hk := congrArg (fun t : T ⟶ G => t.left ≫ φ) key
  rw [← hk, Over.comp_left, Category.assoc, up_left]
  exact ((pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)).symm

end GaloisDescent

open GaloisDescent

theorem abelianScheme_descends_galoisCover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ X Y π sY Ga _ ρ G _ ν hc hq hab hν hν1 hνmul
  obtain ⟨hcomm, hsm, hpr, hgc⟩ := hab
  have := hc.finite
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have hdown : ∀ a, ν a ≫ G.hom = G.hom ≫ ρ a := fun a => (hν a).1.w
  have hinvG : ∀ a, ν a ≫ G.hom ≫ π = G.hom ≫ π := fun a => by
    rw [← Category.assoc, hdown, Category.assoc, hc.inv]
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ G.left) (a : Ga), y ≫ ν a = y → a = 1 := by
    intro k _ _ y a hy
    have hya : (y ≫ G.hom) ≫ ρ a = y ≫ G.hom := by
      rw [Category.assoc, ← hdown, ← Category.assoc, hy]
    have hy1 : (y ≫ G.hom) ≫ ρ 1 = y ≫ G.hom := by rw [hc.one, Category.comp_id]
    exact (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique hya hy1
  obtain ⟨Y₀, π₀, sY₀, -, hc₀, -, -, -⟩ := _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver K G.left (G.hom ≫ π ≫ sY) Ga ν hq hν1 hνmul
    (fun a => by rw [← Category.assoc G.hom π sY, ← Category.assoc, hinvG]) hfree
  obtain ⟨v, hv, -⟩ := (_root_.GlobalTheory.ZM.galoisCover_descent G.left Y₀ π₀ Ga ν hc₀).1 Y (G.hom ≫ π) hinvG
  have hsq : IsPullback G.hom π₀ π v :=
    ((_root_.GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hc).2.2 G.left Y₀ π₀ ν G.hom v hdown hv.symm).1 hc₀
  have H : IsPullback π₀ G.hom (Over.mk v).hom π := hsq.flip
  obtain ⟨inst, hcomm', hgp⟩ := exists_grpObj (G' := Over.mk v) (φ := π₀) hc H hν (fun a => hc₀.inv a)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) π :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsm' : Smooth v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ hsm
  have huc : UniversallyClosed v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have hlft : LocallyOfFiniteType v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have : Surjective π₀ := hc₀.onto
  have : IsFinite π₀ := hc₀.fin
  have : IsSeparated (π₀ ≫ v) := by rw [hv]; infer_instance
  have hsep : IsSeparated v := GlobalTheory.SemiAbelianDescent.isSeparated_of_comp π₀ v
  have hgc' : GeometricallyConnected v := GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback H
  exact ⟨Over.mk v, inst, π₀, ⟨hcomm', hsm', { toIsSeparated := hsep, toUniversallyClosed := huc, toLocallyOfFiniteType := hlft }, hgc'⟩, hgp, hc₀⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChartPullCompOfPullPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

def chartPullCompOfPullPull {X Y Z : Scheme.{0}} (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    ChartPull (M.pull (φ ≫ π)) ((M.pull π).pull φ) (𝟙 Z) where
  idx j := fun _ => j
  le j := RepBC.le₂ M π φ j
  g y j j' hj hj' := by
    have h := RepBC.le₂ M π φ j hj
    have h' := RepBC.le₂ M π φ j' hj'
    refine (gm_pull_g M (φ ≫ π) (𝟙 Z) y j j' hj hj').trans (Eq.symm ?_)
    refine (gm_pull_g (M.pull π) φ (𝟙 Z) y (fun _ => j) (fun _ => j') h h').trans ?_
    exact gm_pull_g M π (𝟙 Z ≫ φ) y j j' (mem_pull.1 h) (mem_pull.1 h')

theorem lbIso_pullPull_iff {X Y Z : Scheme.{0}} (A : LB Z) (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    LBIso A ((M.pull π).pull φ) ↔ LBIso A (M.pull (φ ≫ π)) :=
  ⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ),
    LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)⟩

theorem fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by
  intro o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩
  obtain ⟨th', hrep', hc⟩ := RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp
  have hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ := fun h => by
    rw [Category.assoc, Over.w (sc h), Category.id_comp]
    exact Category.comp_id _
  let sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z') := fun h =>
    Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)
  have hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left := fun h => hp.lift_fst _ _ _
  have hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _ := fun h => hp.lift_snd _ _ _
  refine ⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩,
    MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩
  · rw [hsc]
    exact Coord.baseChange (hco h) ρ
  · intro K _ _ x s t ht
    obtain ⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    have hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ := by
      rw [h1.w, NearBuild.spMap_comp, Category.assoc]
    have e1 : hp.lift φ _ hw' ≫ π = φ := hp.lift_fst _ _ _
    have e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x := hp.lift_snd _ _ _
    generalize hp.lift φ _ hw' = φ' at e1 e2
    subst e1
    refine ⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · apply hp.hom_ext
      · rw [Category.assoc, h4, NearBuild.spMap_comp]
        erw [Category.assoc, Category.assoc, hsc]
      · rw [Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')]
        erw [Category.assoc, hsc', Category.id_comp]
  · rintro K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩
    refine ⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · rw [← Category.assoc, h4, NearBuild.spMap_comp]
      erw [Category.assoc, Category.assoc, hsc]

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstFnZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Cocycle

theorem rsT_of_le {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = (Y.presheaf.map (homOfLE h).op).hom s := by
  unfold rsT; rw [dite_eq_left h]

theorem rsT_rsT {Y : Scheme.{0}} {O₀ O₁ O₂ : Y.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h', rsT_of_le h, rsT_of_le (h'.trans h), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_add {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s + t) O = rsT s O + rsT t O := by
  simp only [rsT_of_le h, map_add (f := _)]

theorem rsT_sub {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s - t) O = rsT s O - rsT t O := by
  simp only [rsT_of_le h, map_sub]

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_zero' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    constFn q O (0 : K) = 0 := by
  simp [constFn]

theorem locDerK_sub {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h₁.add W (hW.trans l₁), h₂.add W (hW.trans l₂)]; ring
  · intro W hW f f'
    rw [h₁.mul W (hW.trans l₁), h₂.mul W (hW.trans l₂)]; ring
  · intro W W' h hW f
    rw [h₁.res W W' h (hW.trans l₁), h₂.res W W' h (hW.trans l₂), rsT_sub (m.preimage_mono h)]
  · intro W hW r
    rw [h₁.base W (hW.trans l₁), h₂.base W (hW.trans l₂), sub_self, constFn_zero']

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact _root_.GlobalTheory.InvFieldBasis.existsUnique_coeff K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem exists_ksCoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp hsp D I W hD hW
  choose d hder using fun i => _root_.GlobalTheory.KS.exists_locDerK_of_smooth K R x₀ A₀.left X A₀.hom p m D (W i) hsp hp.w hD (hW i)
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose c hc using fun i j => (hb (W i ⊓ W j) _ (locDerK_sub (hder i) (hder j) inf_le_left inf_le_right)).exists
  have e : ∀ i j, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := fun i j => rfl
  have e3 : ∀ i j k, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j ⊓ m ⁻¹ᵁ W k = m ⁻¹ᵁ (W i ⊓ W j ⊓ W k) := fun i j k => rfl
  refine ⟨d, fun a i j => rsT (c i j a) _, ⟨hder, ?_⟩, ?_⟩
  · intro i j O hO f
    rw [hc i j O hO f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rsT_rsT (e i j).le ((m.preimage_mono hO).trans (e i j).ge)]
  · intro a i j k
    have lij : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j := inf_le_left
    have ljk : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k := inf_le_inf_right _ inf_le_right
    have lik : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k := inf_le_inf_right _ inf_le_left
    have hu := (hb (W i ⊓ W j ⊓ W k) _
      (locDerK_sub (hder i) (hder k) (lik.trans inf_le_left) inf_le_right)).unique
      (y₁ := fun a => rsT (c i j a) _ + rsT (c j k a) _) (y₂ := fun a => rsT (c i k a) _)
      (by
        intro O hO f
        have h1 := hc i j O (hO.trans lij) f
        have h2 := hc j k O (hO.trans ljk) f
        have : d k O f - d i O f = (d j O f - d i O f) + (d k O f - d j O f) := by ring
        rw [this, h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_add (m.preimage_mono hO), rsT_rsT (m.preimage_mono lij) (m.preimage_mono hO),
          rsT_rsT (m.preimage_mono ljk) (m.preimage_mono hO), add_mul])
      (by
        intro O hO f
        rw [hc i k O (hO.trans lik) f]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_rsT (m.preimage_mono lik) (m.preimage_mono hO)])
    rw [rsT_rsT (e i j).le inf_le_left, rsT_rsT (e j k).le (inf_le_inf_right _ inf_le_right),
      rsT_rsT (e i k).le (inf_le_inf_right _ inf_le_left)]
    exact congrFun hu a

end GlobalTheory.KS.Cocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  first | exact @GlobalTheory.exists_dense_sharp_all_matrices | exact GlobalTheory.exists_dense_sharp_all_matrices | (intros; apply GlobalTheory.exists_dense_sharp_all_matrices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  first | exact @GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | (intros; apply GlobalTheory.LinDescent.exists_descent_of_isGaloisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothDescentOfTameQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst G.hom x ≫ (τ g).asIso.hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).asIso.hom ≫ φ = φ := by
  intro Γ _ _ R _ X X' _ ρ π G s τ hπ hfin hqp hsm hτ hstab hfib
  have hsepG : G.left.IsSeparated := by
    obtain ⟨N, i, hi, -, hcomp⟩ := hqp
    haveI := isProper_str R N
    haveI : IsSeparated (G.hom ≫ s) := by rw [← hcomp]; infer_instance
    constructor
    rw [show terminal.from G.left = (G.hom ≫ s) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨Y', φ, hφ⟩ := exists_quotient_of_finite_group Γ G.left τ (fun y => by
    obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver R G.left (G.hom ≫ s) hqp
      (Set.range fun g => (τ g).asIso.hom y) ⊤ (Set.finite_range _) (fun _ _ => trivial)
    exact ⟨V, hV, fun g => hF ⟨g, rfl⟩⟩)
  obtain ⟨p', hp', -⟩ := quotient_existsUnique_comp_eq Γ G.left Y' τ φ hφ X' (G.hom ≫ π)
    (fun g => by rw [← Category.assoc, hτ g, Category.assoc, hπ.2.1 g])
  obtain ⟨hpb, hflat, hlft⟩ := _root_.GlobalTheory.TameDescent.isPullback_flat_of_tame Γ X X' G.left Y' ρ τ π φ G.hom p' hπ hφ hp' hτ hfin
    inferInstance inferInstance hstab hfib
  have hsurj : Surjective π := (quotient_isIntegral_surjective_orbits Γ X X' ρ π hπ).2.1
  haveI : LocallyOfFinitePresentation p' := inferInstance
  exact ⟨Over.mk p', φ, hpb,
    smooth_of_isPullback_of_surjective_of_flat X X' G.left Y' π φ G.hom p' hpb hsurj hflat
      inferInstance hsm, fun g => hφ.2.1 g⟩

end GlobalTheory
end

