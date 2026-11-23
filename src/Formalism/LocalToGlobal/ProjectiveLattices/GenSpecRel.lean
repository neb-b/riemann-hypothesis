module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace Formalism.L2.Pj.GSR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  have e : w.left ≫ F = w'.left ≫ F :=
    (h : w.left ≫ F = _).trans (h' : w'.left ≫ F = _).symm
  exact Over.OverMorphism.ext (hc.1.hom_ext e (by rw [Over.w w, Over.w w']))

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  have e : v.left ≫ pullback.fst G.hom g = v'.left ≫ pullback.fst G.hom g :=
    (h : _ = v.left ≫ pullback.fst G.hom g).symm.trans (h' : _ = v'.left ≫ pullback.fst G.hom g)
  refine Over.OverMorphism.ext (pullback.hom_ext e ?_)
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have hv' : v'.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v'
  rw [hv, hv']


include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  have cond : (w.left ≫ F) ≫ G.hom = X.hom ≫ g := by
    rw [Category.assoc, hc.1.w, reassoc_of% hw, hg]
  exact ⟨Over.homMk (pullback.lift _ _ cond) (pullback.lift_snd _ _ cond), (pullback.lift_fst _ _ cond).symm⟩

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    ext
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact (h : w.left ≫ F = _).symm
  · intro h
    have e : (pushPt (isGrpPullback_pullback G g).1.w v).left = (iota2 hg X ≫ pushPt hc.1.w w).left := by
      rw [h]
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp] at e
    exact e.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg] at h h' ⊢
  have e1 := map_mul (pushHom (isGrpPullback_pullback G g) X) v v'
  have e2 := map_mul ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X))) w w'
  exact e1.trans ((congrArg₂ (· * ·) h h').trans e2.symm)

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg]
  exact (map_one (pushHom (isGrpPullback_pullback G g) X)).trans
    (map_one ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X)))).symm

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  show (φ.left ≫ w.left) ≫ F = (φ.left ≫ v.left) ≫ pullback.fst G.hom g
  rw [Category.assoc, Category.assoc, (h : w.left ≫ F = _)]

end Corr

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)




end Count

end Formalism.L2.Pj.GSR
