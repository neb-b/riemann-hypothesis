module

public import Development.EtaleCohomology.KummerTheory.Bundle0002
public import Development.EtaleCohomology.KummerTheory.FinalTheorems

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.ExactPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ExactPf

open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (F.obj.map g.op ≫ φ.hom.app (op V)).hom x = (φ.hom.app (op U) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (a : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.res g x) = Sec.res (a ≫ g) x := by
  change _ = (F.obj.map (a ≫ g).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (s : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) s) = 0 := by
  change (Sec.map (I.d i j ≫ I.d j k) s) = 0
  rw [I.d_comp_d]
  rfl

theorem mneg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map φ (-x) = -Sec.map φ x :=
  map_neg _ _

theorem mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem rneg {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.res g (-x) = -Sec.res g x :=
  map_neg _ _

theorem msub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _

theorem rsub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x - y) = Sec.res g x - Sec.res g y :=
  map_sub _ _ _

theorem rzero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem inj (F : Shv R) (m : ℤ) : Injective ((res R F).X m) := by
  unfold res; infer_instance

theorem tr (I : Cx R) {X : Scheme.{0}} (m k j : ℤ) (h : m = k) (a : Sec (I.X j) X) :
    (∃ b : Sec (I.X m) X, Sec.map (I.d m j) b = a) → ∃ b : Sec (I.X k) X, Sec.map (I.d k j) b = a := by
  subst h; exact id

theorem cls_eq (hD : Dict) (F : Shv R) {Y : Scheme.{0}} (m : ℤ) {x y : H R (sch.obj Y) F m}
    {s t : Sec ((res R F).X m) Y} (hx : IsCls x s) (hy : IsCls y t)
    (h : ∃ b : Sec ((res R F).X (m - 1)) Y, Sec.map ((res R F).d (m - 1) m) b = s - t) : x = y := by
  obtain ⟨-, -, D3, D4, -⟩ := hD R (res R F) Y m
  have h3 := (D4 x (-y) s (-t) hx (D4 y y t t hy hy).2).1
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h3
  exact sub_eq_zero.mp ((D3 _ _ h3).2.mpr h)

theorem Exact_of (hD : Dict) (hG : Glue) (hF : Flasque) : Exact := by
  intro R _ F W U V X a b f g hmv n
  have hpb := hmv.2.2.1
  haveI : IsOpenImmersion g := hmv.2.1
  haveI : Mono a := hpb.mono_fst_of_mono
  have hw : a ≫ f = b ≫ g := hpb.w
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
    obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
    have hau : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
    have hbv : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
    rw [huv] at hau
    have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
    have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
    obtain ⟨r, hr⟩ : ∃ r : Sec ((res R F).X (n - 1)) W,
        Sec.map ((res R F).d (n - 1) n) r = Sec.res a u0 - Sec.res b v0 := by
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hau ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hbv hbv).2).1
      rw [add_neg_cancel, ← sub_eq_add_neg] at h3
      exact ((hD R (res R F) W n).2.2.1 _ _ h3).2.mp rfl
    haveI := inj F (n - 1)
    obtain ⟨r', hr'⟩ := hF R ((res R F).X (n - 1)) a r
    change Sec.res a r' = r at hr'
    have hu1 : Sec.res a (u0 - Sec.map ((res R F).d (n - 1) n) r') = Sec.res b v0 := by
      rw [rsub]
      rw [← map_res, hr', hr]
      abel
    obtain ⟨z, hzf, hzg⟩ := (hG R ((res R F).X n) a b f g hmv).2 _ v0 hu1
    have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := by
      apply (hG R ((res R F).X (n + 1)) a b f g hmv).1
      · rw [← map_res, hzf, msub, hu0c, dd, sub_zero]
      · rw [← map_res, hzg, hv0c]
    obtain ⟨x, hx⟩ := (hD R (res R F) X n).1 z hdz
    refine ⟨x, ?_, ?_⟩
    · have hfx : IsCls (pull R (sch.map f) F n x) (Sec.res f z) := (hD R (res R F) X n).2.2.2.2 f x z hx
      rw [hzf] at hfx
      refine cls_eq hD F n hfx hu0 ⟨-r', ?_⟩
      rw [mneg]
      abel
    · have hgx : IsCls (pull R (sch.map g) F n x) (Sec.res g z) := (hD R (res R F) X n).2.2.2.2 g x z hx
      rw [hzg] at hgx
      exact cls_eq hD F n hgx hv0 ⟨0, by rw [mzero, sub_self]⟩
  · intro x hfx hgx
    obtain ⟨z0, hz0⟩ := (hD R (res R F) X (n + 1)).2.1 x
    have hz0c := ((hD R (res R F) X (n + 1)).2.2.1 x z0 hz0).1
    have hgz : IsCls (pull R (sch.map g) F (n + 1) x) (Sec.res g z0) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 g x z0 hz0
    rw [hgx] at hgz
    obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) V (n + 1)).2.2.1 _ _ hgz).2.mp rfl)
    haveI := inj F n
    obtain ⟨t', ht'⟩ := hF R ((res R F).X n) g t
    change Sec.res g t' = t at ht'
    have hzg : Sec.res g (z0 - Sec.map ((res R F).d n (n + 1)) t') = 0 := by
      rw [rsub, ← map_res, ht', ht, sub_self]
    obtain ⟨x', hx'⟩ := (hD R (res R F) X (n + 1)).1 (z0 - Sec.map ((res R F).d n (n + 1)) t')
      (by rw [msub, hz0c, dd, sub_zero])
    have hxx : x' = x := cls_eq hD F (n + 1) hx' hz0
      (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t', by rw [mneg]; abel⟩)
    rw [hxx] at hx'
    have hfz : IsCls (pull R (sch.map f) F (n + 1) x) (Sec.res f (z0 - Sec.map ((res R F).d n (n + 1)) t')) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 f x _ hx'
    rw [hfx] at hfz
    obtain ⟨s, hs⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) U (n + 1)).2.2.1 _ _ hfz).2.mp rfl)
    have hsc : Sec.map ((res R F).d n (n + 1)) (Sec.res a s) = 0 := by
      rw [map_res, hs, res_res, hw, ← res_res, hzg, rzero]
    obtain ⟨w, hw'⟩ := (hD R (res R F) W n).1 _ hsc
    exact ⟨w, s, _, hw', hx', hs.symm, hzg⟩
  · intro w
    constructor
    · rintro ⟨s, z, hws, hz0, hfz, hgz⟩
      obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
        (((hD R (res R F) X (n + 1)).2.2.1 _ _ hz0).2.mp rfl)
      have hu : Sec.map ((res R F).d n (n + 1)) (s - Sec.res f t) = 0 := by
        rw [msub, map_res, ht, hfz, sub_self]
      have hv : Sec.map ((res R F).d n (n + 1)) (-Sec.res g t) = 0 := by
        rw [mneg, map_res, ht, hgz, neg_zero]
      obtain ⟨u, hu'⟩ := (hD R (res R F) U n).1 _ hu
      obtain ⟨v, hv'⟩ := (hD R (res R F) V n).1 _ hv
      refine ⟨u, v, ?_⟩
      have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a (s - Sec.res f t)) :=
        (hD R (res R F) U n).2.2.2.2 a u _ hu'
      have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b (-Sec.res g t)) :=
        (hD R (res R F) V n).2.2.2.2 b v _ hv'
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
      have hA : Sec.res a (s - Sec.res f t) + -Sec.res b (-Sec.res g t) = Sec.res a s := by
        rw [rsub, rneg, res_res, res_res, hw]
        abel
      rw [hA, ← sub_eq_add_neg] at h3
      exact cls_eq hD F n hws h3 ⟨0, by rw [mzero, sub_self]⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
      obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
      have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
      have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
      haveI := inj F n
      obtain ⟨s', hs'⟩ := hF R ((res R F).X n) a (Sec.res b v0)
      change Sec.res a s' = Sec.res b v0 at hs'
      obtain ⟨t, htf, htg⟩ := (hG R ((res R F).X n) a b f g hmv).2 s' v0 hs'
      refine ⟨u0 - s', -Sec.map ((res R F).d n (n + 1)) t, ?_, ?_, ?_, ?_⟩
      · have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
        have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
        have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← hs', ← rsub] at h3
        exact h3
      · obtain ⟨y, hy⟩ := (hD R (res R F) X (n + 1)).1 (-Sec.map ((res R F).d n (n + 1)) t)
          (by rw [mneg, dd, neg_zero])
        have hy0 : y = 0 := ((hD R (res R F) X (n + 1)).2.2.1 _ _ hy).2.mpr
          (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t, mneg _ _⟩)
        rw [hy0] at hy
        exact hy
      · rw [rneg, ← map_res, htf, msub, hu0c, zero_sub]
      · rw [rneg, ← map_res, htg, hv0c, neg_zero]

end LateralTheory.KummerTheory.ExactPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.FivePf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.KummerTheory.FivePf
open LateralTheory.KummerTheory.ContCut

variable {K : Type 1} [Category.{0} K]

theorem mapc (G : K ⥤ AddCommGrpCat.{1}) {a b d : K} (f : a ⟶ b) (g : b ⟶ d) (x : G.obj a) :
    (G.map g).hom ((G.map f).hom x) = (G.map (f ≫ g)).hom x := by
  rw [G.map_comp]; rfl

theorem natap {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) {k k' : K} (h : k ⟶ k') (x : F.obj k) :
    (α.app k').hom ((F.map h).hom x) = (G.map h).hom ((α.app k).hom x) := by
  have := congrArg (fun φ => φ.hom x) (α.naturality h)
  exact this

theorem commap {X U V W : ℤ → K ⥤ AddCommGrpCat.{1}} (S : MVSeq X U V W) (n : ℤ) (k : K) (x : (X n).obj k) :
    ((S.a n).app k).hom (((S.f n).app k).hom x) = ((S.b n).app k).hom (((S.g n).app k).hom x) := by
  have := congrArg (fun φ => (φ.app k).hom x) (S.comm n)
  exact this

variable {J : Type} [SmallCategory J] {D : J ⥤ K}

theorem natι {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) (c : Cocone D) (j : J) (x : F.obj (D.obj j)) :
    (α.app c.pt).hom ((F.map (c.ι.app j)).hom x) = (G.map (c.ι.app j)).hom ((α.app (D.obj j)).hom x) :=
  natap α (c.ι.app j) x

theorem push (G : K ⥤ AddCommGrpCat.{1}) (c : Cocone D) {j k : J} (f : j ⟶ k) (y : G.obj (D.obj j)) :
    (G.map (c.ι.app k)).hom ((G.map (D.map f)).hom y) = (G.map (c.ι.app j)).hom y := by
  rw [mapc, c.w]

theorem five_succ [IsFiltered J] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) (S : MVSeq X U V W) (c : Cocone D)
    (hU : ∀ n, Lim (U n) c) (hV : ∀ n, Lim (V n) c) (hW : ∀ n, Lim (W n) c) (m : ℤ) : Lim (X (m + 1)) c := by
  constructor
  · intro x
    obtain ⟨j1, u, hu⟩ := (hU (m + 1)).1 (((S.f (m + 1)).app c.pt).hom x)
    obtain ⟨j2, v, hv⟩ := (hV (m + 1)).1 (((S.g (m + 1)).app c.pt).hom x)
    obtain ⟨k, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    have e0 : ((W (m + 1)).map (c.ι.app k)).hom
        (((S.a (m + 1)).app (D.obj k)).hom (((U (m + 1)).map (D.map g1)).hom u) -
          ((S.b (m + 1)).app (D.obj k)).hom (((V (m + 1)).map (D.map g2)).hom v)) = 0 := by
      rw [map_sub, ← natι (S.a (m + 1)), ← natι (S.b (m + 1)), push, push, hu, hv, commap, sub_self]
    obtain ⟨k2, f2, h2⟩ := (hW (m + 1)).2 k _ e0
    rw [map_sub, ← natap (S.a (m + 1)), ← natap (S.b (m + 1)), sub_eq_zero] at h2
    obtain ⟨x', hx1, hx2⟩ := S.exUV (m + 1) (D.obj k2) _ _ h2
    obtain ⟨xi, hxi⟩ : ∃ xi : (X (m + 1)).obj c.pt, xi = ((X (m + 1)).map (c.ι.app k2)).hom x' := ⟨_, rfl⟩
    have hfd : ((S.f (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.f (m + 1)), hx1, push, push, hu, sub_self]
    have hgd : ((S.g (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.g (m + 1)), hx2, push, push, hv, sub_self]
    obtain ⟨w, hw⟩ := S.exX m c.pt _ hfd hgd
    obtain ⟨j3, w0, hw0⟩ := (hW m).1 w
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 j3
    refine ⟨k4, ((X (m + 1)).map (D.map g3)).hom x' + ((X (m + 1)).map (D.map g4)).hom (((S.δ m).app (D.obj j3)).hom w0), ?_⟩
    rw [map_add (f := _), push, push, ← natι (S.δ m), hw0, hw, ← hxi]
    exact add_sub_cancel _ _
  · intro j y hy
    have hfy : ((U (m + 1)).map (c.ι.app j)).hom (((S.f (m + 1)).app (D.obj j)).hom y) = 0 := by
      rw [← natι (S.f (m + 1)), hy, map_zero]
    obtain ⟨k1, f1, h1⟩ := (hU (m + 1)).2 j _ hfy
    have hgy : ((V (m + 1)).map (c.ι.app k1)).hom
        (((V (m + 1)).map (D.map f1)).hom (((S.g (m + 1)).app (D.obj j)).hom y)) = 0 := by
      rw [push, ← natι (S.g (m + 1)), hy, map_zero]
    obtain ⟨k2, f2, h2⟩ := (hV (m + 1)).2 k1 _ hgy
    have hf1 : ((S.f (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h1, map_zero]
    have hg1 : ((S.g (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h2]
    obtain ⟨w, hw⟩ := S.exX m (D.obj k2) _ hf1 hg1
    have hdw : ((S.δ m).app c.pt).hom (((W m).map (c.ι.app k2)).hom w) = 0 := by
      rw [natι (S.δ m), hw, push, hy]
    obtain ⟨u, v, huv⟩ := (S.exW m c.pt _).1 hdw
    obtain ⟨j1, u0, hu0⟩ := (hU m).1 u
    obtain ⟨j2, v0, hv0⟩ := (hV m).1 v
    obtain ⟨k3, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 k3
    have he : ((W m).map (c.ι.app k4)).hom (((W m).map (D.map g3)).hom w -
        (((S.a m).app (D.obj k4)).hom (((U m).map (D.map (g1 ≫ g4))).hom u0) -
          ((S.b m).app (D.obj k4)).hom (((V m).map (D.map (g2 ≫ g4))).hom v0))) = 0 := by
      rw [map_sub, map_sub, push, ← natι (S.a m), ← natι (S.b m), push, push, hu0, hv0, huv, sub_self]
    obtain ⟨k5, g5, h5⟩ := (hW m).2 k4 _ he
    rw [map_sub, sub_eq_zero, mapc, map_sub, ← natap (S.a m), ← natap (S.b m)] at h5
    refine ⟨k5, (f1 ≫ f2) ≫ g3 ≫ g5, ?_⟩
    rw [D.map_comp, ← mapc, ← hw, ← natap (S.δ m), D.map_comp, h5]
    exact (S.exW m _ _).2 ⟨_, _, rfl⟩

theorem Five_of : LateralTheory.KummerTheory.ContCut.Five := by
  intro J _ _ K _ X U V W ⟨S⟩ D c hU hV hW n
  have := five_succ X U V W S c hU hV hW (n - 1)
  rwa [sub_add_cancel] at this

end LateralTheory.KummerTheory.FivePf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.GluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.GluePf

def pc (U V : Scheme.{0}) : Bool → Scheme.{0} := fun b => Bool.rec V U b

def pm {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) : ∀ b : Bool, pc U V b ⟶ X :=
  fun b => Bool.rec (motive := fun b => pc U V b ⟶ X) g f b

theorem mem_cover {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Sieve.generate (Presieve.ofArrows (pc U V) (pm f g)) ∈ Scheme.etaleTopology X := by
  obtain ⟨hf, hg, -, hcov⟩ := h
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
  · rcases hcov x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · cases i
    · exact (inferInstance : Etale g)
    · exact (inferInstance : Etale f)

theorem sheafFor {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (f : U ⟶ X) (g : V ⟶ X) (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Presieve.IsSheafFor (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
      (Presieve.ofArrows (pc U V) (pm f g)) := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  rw [Presieve.isSheafFor_iff_generate]
  exact hG.isSheafFor _ (mem_cover a b f g h)

theorem compat {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V}
    {f : U ⟶ X} {g : V ⟶ X} (hpb : IsPullback a b f g) {s : Sec G U} {t : Sec G V}
    (hst : Sec.res a s = Sec.res b t) {Z : Scheme.{0}} (gi : Z ⟶ U) (gj : Z ⟶ V) (e : gi ≫ f = gj ≫ g) :
    (G.obj.map gi.op).hom s = (G.obj.map gj.op).hom t := by
  obtain ⟨l, hl1, hl2⟩ := hpb.exists_lift gi gj e
  subst hl1 hl2
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (G.obj.map l.op).hom hst

theorem Glue_of : LateralTheory.KummerTheory.ContCut.Glue := by
  intro R _ G W U V X a b f g h
  have hS := sheafFor G a b f g h
  rw [Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨hf, hg, hpb, -⟩ := h
  refine ⟨fun z hz1 hz2 => ?_, fun s t hst => ?_⟩
  · have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g)
        (fun _ => (0 : Sec G _)) := by
      intro i j Z gi gj _
      change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
      simp
    obtain ⟨t, -, ht⟩ := hS _ hc
    have e1 := ht z (fun i => by cases i <;> assumption)
    have e2 := ht 0 (fun i => by
      change (G.obj.map _).hom 0 = 0
      simp)
    rw [e1, e2]
  · let x : ∀ i, Sec G (pc U V i) := fun i => Bool.rec (motive := fun i => Sec G (pc U V i)) t s i
    have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) x := by
      intro i j Z gi gj e
      change (G.obj.map gi.op).hom (x i) = (G.obj.map gj.op).hom (x j)
      cases i <;> cases j
      · have : gi = gj := (cancel_mono g).1 e
        subst this; rfl
      · exact (compat G hpb hst gj gi e.symm).symm
      · exact compat G hpb hst gi gj e
      · have : gi = gj := (cancel_mono f).1 e
        subst this; rfl
    obtain ⟨z, hz, -⟩ := hS x hc
    exact ⟨z, hz true, hz false⟩

end LateralTheory.KummerTheory.GluePf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.HomKillPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.HomKillPf
open LateralTheory.KummerTheory.LHCut

lemma cover_mem {S : Scheme.{0}} {U : Over S} (V : U.left → Over S) (g : ∀ u, V u ⟶ U)
    (hg : ∀ u, Nbhd (g u) u) : Sieve.ofArrows V g ∈ (Scheme.etaleTopology.over S) U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ⟨x, ?_⟩, fun u => (hg u).1⟩
  obtain ⟨v, hv⟩ := (hg x).2
  exact ⟨v, hv⟩

lemma inj_app {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {F G : SlShv Λ S} (f : F ⟶ G) [Mono f]
    (U : Over S) : Function.Injective (f.hom.app (op U)).hom := by
  rw [← ModuleCat.mono_iff_injective]
  have : Mono ((sheafToPresheaf _ _).map f) := inferInstance
  exact (NatTrans.mono_iff_mono_app _).1 this (op U)

variable {Λ : Type} [CommRing Λ] {S : Scheme.{0}}

lemma sec_eq_zero (F : SlShv Λ S) {U : Over S}
    (s : F.obj.obj (op U)) (R : Sieve U) (hR : R ∈ (Scheme.etaleTopology.over S) U)
    (h : ∀ (W : Over S) (f : W ⟶ U), R f → (F.obj.map f.op).hom s = 0) : s = 0 := by
  apply F.isSeparated U R hR s 0
  intro W f hf
  rw [h W f hf, map_zero]

lemma nsmul_app {F G : SlShv Λ S} (f : F ⟶ G) (N : ℕ)
    (U : Over S) (x : F.obj.obj (op U)) :
    ((N • f).hom.app (op U)).hom x = N • (f.hom.app (op U)).hom x := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

lemma comp_sec {F G H : SlShv Λ S} (f : F ⟶ G) (g : G ⟶ H) (U : Over S) (x : F.obj.obj (op U)) :
    ((f ≫ g).hom.app (op U)).hom x = (g.hom.app (op U)).hom ((f.hom.app (op U)).hom x) := rfl

lemma nat_sec {F G : SlShv Λ S} (f : F ⟶ G) {U V : Over S} (g : V ⟶ U) (x : F.obj.obj (op U)) :
    (f.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((f.hom.app (op U)).hom x) := by
  have := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simpa using this

lemma hom_eq_zero {F G : SlShv Λ S} (f : F ⟶ G)
    (h : ∀ (U : Over S) (x : F.obj.obj (op U)), (f.hom.app (op U)).hom x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem homKill_of : HomKill := by
  intro Λ _ S C N j hloc
  rw [← cancel_epi (C.homologyπ j), comp_zero, Preadditive.comp_nsmul, Category.comp_id]
  apply hom_eq_zero
  intro U z
  rw [nsmul_app]
  have hx : ((C.d j (j + 1)).hom.app (op U)).hom ((C.iCycles j).hom.app (op U) |>.hom z) = 0 := by
    rw [← comp_sec, C.iCycles_d]; rfl
  choose V g hg y hy using hloc U _ hx
  apply sec_eq_zero _ _ (Sieve.ofArrows V g) (cover_mem V g hg)
  rintro W f ⟨Y, h, _, ⟨u⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  convert map_zero ((C.homology j).obj.map h.op).hom
  rw [map_nsmul, ← nat_sec, ← map_nsmul]
  have key : N • ((C.cycles j).obj.map (g u).op).hom z = ((C.toCycles (j - 1) j).hom.app (op (V u))).hom (y u) := by
    apply inj_app (C.iCycles j)
    rw [← comp_sec, C.toCycles_i, hy u, map_nsmul, nat_sec]
  rw [key, ← comp_sec, C.toCycles_comp_homologyπ]; rfl

end LateralTheory.KummerTheory.HomKillPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.LhNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LhNatPf

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_fst, Category.comp_id]

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_snd]

theorem pull_pull (q : ℕ) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {n i : ℤ} (x : Ht q E'' n i) :
    pull _ f _ _ (pull _ g _ _ x) = pull _ (f ≫ g) _ _ x := (pull_comp _ f g _ _ x).symm

theorem lhNat_of : LateralTheory.KummerTheory.LHCut.LhNat := by
  intro hA q _ X S p i r c M n V U g y
  unfold LateralTheory.KummerTheory.lh
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
  unfold LateralTheory.KummerTheory.ext
  rw [pull_cast, (hA q).1, pull_pull, pull_pull, pull_pull, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, rst_fst, rst_snd]

end LateralTheory.KummerTheory.LhNatPf
end
end

