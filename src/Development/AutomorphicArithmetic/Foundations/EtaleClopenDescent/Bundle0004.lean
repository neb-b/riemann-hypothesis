module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0034
public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.LeafShMapZeroOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleStalkCohomologyStrictHenselianContinuity
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf LateralTheory.E.LeafVanBStalkPf

namespace UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices

section DiagramChase₂
variable (R : Type) [CommRing R]

private abbrev bd {Z E : Spc} (f : Z ⟶ E) (F : Shv R) (n : ℤ) : H R Z F n →+ Hrel R f F (n + 1) :=
  HK.pre R (mappingCone.fst ((chains R).map f)) F n (n + 1) (add_comm 1 n)

private theorem bd_nat {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) (b : H R U F n) :
    rpull R f f' u e comm F (n + 1) (bd R f F n b) = bd R f' F n (pull R u F n b) := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]

private theorem bd_pull {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (a : H R E F n) :
    bd R f F n (pull R f F n a) = 0 :=
  (coneSeq_exact R ((chains R).map f) (res R F) n).2.1.apply_apply_eq_zero a

private theorem exists_pull {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (b : H R U F n)
    (h : bd R f F n b = 0) : ∃ a : H R E F n, pull R f F n a = b :=
  ((coneSeq_exact R ((chains R).map f) (res R F) n).2.1 b).1 h

private theorem exists_bd {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F (n + 1))
    (h : fgt R f F (n + 1) y = 0) : ∃ b : H R U F n, bd R f F n b = y :=
  ((coneSeq_exact R ((chains R).map f) (res R F) n).2.2 y).1 h

private theorem relCont {J : Type} [SmallCategory J] [IsFiltered J] (F : Shv R) {Ei Zi : Spc} (fi : Zi ⟶ Ei)
    (E Z : J → Spc) (f : ∀ j, Z j ⟶ E j)
    (eM : ∀ {j j' : J}, (j ⟶ j') → (E j' ⟶ E j)) (zM : ∀ {j j' : J}, (j ⟶ j') → (Z j' ⟶ Z j))
    (sq : ∀ {j j' : J} (g : j ⟶ j'), f j' ≫ eM g = zM g ≫ f j)
    (fe : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), eM (g ≫ g') = eM g' ≫ eM g)
    (fz : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), zM (g ≫ g') = zM g' ≫ zM g)
    (te : ∀ j, Ei ⟶ E j) (tz : ∀ j, Zi ⟶ Z j) (sqt : ∀ j, fi ≫ te j = tz j ≫ f j)
    (ce : ∀ {j j' : J} (g : j ⟶ j'), te j' ≫ eM g = te j)
    (cz : ∀ {j j' : J} (g : j ⟶ j'), tz j' ≫ zM g = tz j)
    (CEi : ∀ (n : ℤ) (j : J) (y : H R (E j) F n), pull R (te j) F n y = 0 →
      ∃ (j' : J) (g : j ⟶ j'), pull R (eM g) F n y = 0)
    (CEs : ∀ (n : ℤ) (x : H R Ei F n), ∃ (j : J) (y : H R (E j) F n), pull R (te j) F n y = x)
    (CZi : ∀ (n : ℤ) (j : J) (y : H R (Z j) F n), pull R (tz j) F n y = 0 →
      ∃ (j' : J) (g : j ⟶ j'), pull R (zM g) F n y = 0)
    (n : ℤ) (j : J) (c : Hrel R (f j) F (n + 1))
    (hc : rpull R (f j) fi (tz j) (te j) (sqt j) F (n + 1) c = 0) :
    ∃ (j' : J) (g : j ⟶ j'), rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) c = 0 := by

  have cmp1 : ∀ {j j' : J} (g : j ⟶ j') (y : Hrel R (f j) F (n + 1)),
      rpull R (f j') fi (tz j') (te j') (sqt j') F (n + 1) (rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) y) =
        rpull R (f j) fi (tz j) (te j) (sqt j) F (n + 1) y := by
    intro j j' g y
    have c3 : fi ≫ (te j' ≫ eM g) = (tz j' ≫ zM g) ≫ f j := by
      rw [ce, cz, sqt]
    rw [← rpull_comp R (f j) (f j') fi (zM g) (eM g) (tz j') (te j') (sq g) (sqt j') c3]
    exact congrFun (congrArg _ rfl) y |>.trans (by
      rw [rpull_congr R (f j) fi (cz g) (ce g) c3 (sqt j)])
  have cmp2 : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j'') (y : Hrel R (f j) F (n + 1)),
      rpull R (f j') (f j'') (zM g') (eM g') (sq g') F (n + 1) (rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) y) =
        rpull R (f j) (f j'') (zM (g ≫ g')) (eM (g ≫ g')) (sq (g ≫ g')) F (n + 1) y := by
    intro j j' j'' g g' y
    have c3 : f j'' ≫ (eM g' ≫ eM g) = (zM g' ≫ zM g) ≫ f j := by
      rw [← fe, ← fz, sq]
    rw [← rpull_comp R (f j) (f j') (f j'') (zM g) (eM g) (zM g') (eM g') (sq g) (sq g') c3]
    rw [rpull_congr R (f j) (f j'') (fz g g').symm (fe g g').symm c3 (sq (g ≫ g'))]

  have h1 : pull R (te j) F (n + 1) (fgt R (f j) F (n + 1) c) = 0 := by
    rw [← relNat R F (f j) fi (tz j) (te j) (sqt j) (n + 1) c, hc, map_zero]
  obtain ⟨j1, g1, h2⟩ := CEi (n + 1) j _ h1
  set c1 := rpull R (f j) (f j1) (zM g1) (eM g1) (sq g1) F (n + 1) c with hc1
  have h3 : fgt R (f j1) F (n + 1) c1 = 0 := by
    rw [hc1, relNat R F (f j) (f j1) (zM g1) (eM g1) (sq g1) (n + 1) c, h2]
  obtain ⟨b, hb⟩ := exists_bd R (f j1) F n c1 h3

  have h4 : bd R fi F n (pull R (tz j1) F n b) = 0 := by
    rw [← bd_nat R (f j1) fi (tz j1) (te j1) (sqt j1) F n b, hb, hc1, cmp1, hc]
  obtain ⟨ai, hai⟩ := exists_pull R fi F n _ h4
  obtain ⟨j2, a2, ha2⟩ := CEs n ai

  let j3 := IsFiltered.max j1 j2
  let g3 : j1 ⟶ j3 := IsFiltered.leftToMax j1 j2
  let g3' : j2 ⟶ j3 := IsFiltered.rightToMax j1 j2
  set a3 := pull R (eM g3') F n a2 with ha3
  set d := pull R (zM g3) F n b - pull R (f j3) F n a3 with hd
  have h5 : pull R (tz j3) F n d = 0 := by
    rw [hd, map_sub, ← pull_comp, ← pull_comp, cz, ← sqt, pull_comp, ha3, ← pull_comp R (te j3), ce, ha2, hai,
      sub_self]
  obtain ⟨j4, g4, h6⟩ := CZi n j3 d h5
  refine ⟨j4, g1 ≫ g3 ≫ g4, ?_⟩
  rw [← cmp2 g1 (g3 ≫ g4), ← hc1, ← hb, bd_nat, fz, pull_comp]
  have h7 : pull R (zM g4) F n (pull R (zM g3) F n b) = pull R (zM g4) F n (pull R (f j3) F n a3) := by
    rw [hd, map_sub, sub_eq_zero] at h6
    exact h6
  rw [h7, ← pull_comp, ← sq g4, pull_comp, bd_pull]

end DiagramChase₂

section Transport

private theorem injT (hB : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (hc : IsColimit c) (X : J → Scheme.{0}) (ex : ∀ j, X j ≅ Spec (D.obj j))
    (tr : ∀ {j j' : J}, (j ⟶ j') → (X j' ⟶ X j))
    (htr : ∀ {j j' : J} (g : j ⟶ j'), (ex j').inv ≫ tr g ≫ (ex j).hom = Spec.map (D.map g))
    (tl : ∀ j, Spec c.pt ⟶ X j) (htl : ∀ j, tl j ≫ (ex j).hom = Spec.map (c.ι.app j))
    (hu : ∀ j, IsUnit (q : D.obj j)) (n : ℤ) (j : J) (y : Ht q (sch.obj (X j)) n i)
    (hy : pl q i (tl j) n y = 0) : ∃ (j' : J) (g : j ⟶ j'), pl q i (tr g) n y = 0 := by
  have h0 : pl q i (Spec.map (c.ι.app j)) n (pl q i (ex j).inv n y) = 0 := by
    rw [← pl_comp, ← htl, Category.assoc, Iso.hom_inv_id, Category.comp_id, hy]
  obtain ⟨j', g, h1⟩ := (hB q D c hc n i).2 j (pl q i (ex j).inv n y) (hu j) h0
  refine ⟨j', g, ?_⟩
  have h2 : pl q i (Spec.map (D.map g)) n (pl q i (ex j).inv n y) = 0 := h1
  rw [← pl_comp, ← htr, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, pl_comp] at h2
  have h3 := congrArg (pl q i (ex j').hom n) h2
  rw [← pl_comp, Iso.hom_inv_id, map_zero] at h3
  simpa [pl, pull_id] using h3

private theorem surjT (hB : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (hc : IsColimit c) (X : J → Scheme.{0}) (ex : ∀ j, X j ≅ Spec (D.obj j))
    (tl : ∀ j, Spec c.pt ⟶ X j) (htl : ∀ j, tl j ≫ (ex j).hom = Spec.map (c.ι.app j))
    (hu : IsUnit (q : c.pt)) (n : ℤ) (x : Ht q (sch.obj (Spec c.pt)) n i) :
    ∃ (j : J) (y : Ht q (sch.obj (X j)) n i), pl q i (tl j) n y = x := by
  obtain ⟨j, y, h⟩ := (hB q D c hc n i).1 x hu
  refine ⟨j, pl q i (ex j).hom n y, ?_⟩
  rw [← pl_comp, htl]
  exact h

private theorem unit_of {k : Type} [Field k] {q : ℕ} (hq : IsUnit (q : k)) (A : CommRingCat.{0})
    (f : Spec A ⟶ Sp k) : IsUnit (q : A) := by
  have g := Spec.preimage f
  simpa using hq.map g.hom

private theorem tr_comp_left {B : Scheme.{0}} {U : B.Etale} {x : U.left} (S : SHSys U x) {j j' j'' : S.J}
    (g : j ⟶ j') (g' : j' ⟶ j'') : (S.tr (g ≫ g')).left = (S.tr g').left ≫ (S.tr g).left := by
  have h := S.tr_spec (g ≫ g')
  rw [Functor.map_comp, Spec.map_comp, ← S.tr_spec g, ← S.tr_spec g'] at h
  have h2 : (S.e j'').inv ≫ (S.tr (g ≫ g')).left ≫ (S.e j).hom =
      (S.e j'').inv ≫ ((S.tr g').left ≫ (S.tr g).left) ≫ (S.e j).hom := by
    rw [h]; simp
  rw [cancel_epi, cancel_mono] at h2
  exact h2

end Transport

theorem main : LateralTheory.E.LeafVanBStalkPf.LeafSHCont := by
  intro hy q _ k _ hq i B W s ι _ U m c x S h0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by ring⟩
  have hB : B1 := hy.2.2.2.2.2.2.2.2.2.2.1

  let tl : ∀ j, Spec S.c.pt ⟶ (S.V j).left := fun j => Spec.map (S.c.ι.app j) ≫ (S.e j).inv
  have htl : ∀ j, tl j ≫ (S.a j).left = S.t := fun j => by simp [tl, S.ht j]
  have htv : ∀ j, tl j ≫ (S.V j).hom = S.t ≫ U.hom := fun j => by
    have hw : (S.a j).left ≫ U.hom = (S.V j).hom := by simpa using (S.a j).w
    rw [← hw, ← Category.assoc, htl]
  let zl : ∀ j, pullback (S.t ≫ U.hom) ι ⟶ pullback (S.V j).hom ι := fun j =>
    pullback.map _ _ _ _ (tl j) (𝟙 W) (𝟙 B) (by simp [htv j]) (by simp)
  have hz1 : ∀ j, zl j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) ≫ (S.e j).inv :=
    fun j => pullback.lift_fst _ _ _
  have hz2 : ∀ j, zl j ≫ pullback.snd _ _ = pullback.snd _ _ := fun j =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  obtain ⟨D', c', hc', ez, ei, hD1, hD2⟩ := UpperTheory.exists_closedFiber_colimit_presentation ι U x S zl hz1 hz2

  have huD : ∀ j, IsUnit (q : S.D.obj j) := fun j => unit_of hq _ ((S.e j).inv ≫ (S.V j).hom ≫ s)
  have huD' : ∀ j, IsUnit (q : D'.obj j) := fun j =>
    unit_of hq _ ((ez j).inv ≫ pullback.snd _ _ ≫ ι ≫ s)
  have huc : IsUnit (q : S.c.pt) := unit_of hq _ (S.t ≫ U.hom ≫ s)
  have c3 : ∀ {j j' : S.J} (g : j ⟶ j'), prB ι (S.V j') ≫ (S.tr g).left = resBW ι (S.tr g) ≫ prB ι (S.V j) :=
    fun g => (pullback.lift_fst _ _ _).symm
  have c4 : ∀ j, pullback.fst (S.t ≫ U.hom) ι ≫ tl j = zl j ≫ prB ι (S.V j) := fun j => (pullback.lift_fst _ _ _).symm
  have ct : ∀ {j j' : S.J} (g : j ⟶ j'), tl j' ≫ (S.tr g).left = tl j := fun {j j'} g => by
    have h1 : Spec.map (S.c.ι.app j) = Spec.map (S.c.ι.app j') ≫ Spec.map (S.D.map g) := by
      rw [← Spec.map_comp, S.c.w g]
    simp only [tl]
    rw [h1, ← S.tr_spec g]
    simp
  obtain ⟨j0⟩ : Nonempty S.J := IsFiltered.nonempty
  have key := relCont (ZMod q) (tw q i) (sch.map (pullback.fst (S.t ≫ U.hom) ι))
    (fun j => sch.obj (S.V j).left) (fun j => sch.obj (pullback (S.V j).hom ι))
    (fun j => sch.map (prB ι (S.V j)))
    (fun g => sch.map (S.tr g).left) (fun g => sch.map (resBW ι (S.tr g)))
    (fun g => by rw [← Functor.map_comp, ← Functor.map_comp, c3 g])
    (fun g g' => by rw [tr_comp_left S g g', Functor.map_comp])
    (fun g g' => by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, tr_comp_left S g g'])
    (fun j => sch.map (tl j)) (fun j => sch.map (zl j))
    (fun j => by rw [← Functor.map_comp, ← Functor.map_comp, c4 j])
    (fun g => by rw [← Functor.map_comp, ct g])
    (fun {j j'} g => by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [zl, resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, ct g])
    (fun n j y h => injT hB q i S.D S.c S.hc (fun j => (S.V j).left) S.e (fun g => (S.tr g).left) (fun g => S.tr_spec g)
      tl (fun j => by simp [tl]) huD n j y h)
    (fun n x => surjT hB q i S.D S.c S.hc (fun j => (S.V j).left) S.e tl (fun j => by simp [tl]) huc n x)
    (fun n j y h => by
      refine injT hB q i D' c' hc' (fun j => pullback (S.V j).hom ι) ez (fun g => resBW ι (S.tr g)) hD1
        (fun j => ei.inv ≫ zl j) (fun j => by simpa using hD2 j) huD' n j y ?_
      rw [pl_comp]
      exact (congrArg _ h).trans (map_zero _))
    n j0 (rB q i ι (S.a j0) (n + 1) c) ?_
  · obtain ⟨j', g, h⟩ := key
    refine ⟨j', ?_⟩
    rw [← S.tr_a g, rB_comp]
    exact h
  · have cu : sch.map (zl j0) ≫ sch.map (resBW ι (S.a j0)) = sch.map (pullback.map (S.t ≫ U.hom) ι U.hom ι S.t (𝟙 W) (𝟙 B)
        (by simp) (by simp)) := by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [zl, resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, htl j0]
    have ce0 : sch.map (tl j0) ≫ sch.map (S.a j0).left = sch.map S.t := by
      rw [← Functor.map_comp, htl]
    have c3' : sch.map (pullback.fst (S.t ≫ U.hom) ι) ≫ (sch.map (tl j0) ≫ sch.map (S.a j0).left) =
        (sch.map (zl j0) ≫ sch.map (resBW ι (S.a j0))) ≫ sch.map (prB ι U) := by
      rw [cu, ce0, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact (pullback.lift_fst _ _ _).symm
    refine (rpull_comp (ZMod q) (sch.map (prB ι U)) (sch.map (prB ι (S.V j0))) (sch.map (pullback.fst _ ι))
      (sch.map (resBW ι (S.a j0))) (sch.map (S.a j0).left) (sch.map (zl j0)) (sch.map (tl j0)) _ _ c3' (tw q i) (n + 1) c).symm.trans ?_
    exact (DFunLike.congr_fun (rpull_congr (ZMod q) _ _ cu ce0 c3' _ (tw q i) (n + 1)) c).trans h0

end UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices

theorem UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity :
    LateralTheory.E.LeafVanBStalkPf.LeafSHCont :=
  UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices.main
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FreeEtaleSheafLiftExists
section
open CategoryTheory Limits

namespace UpperTheory.Cb.HomologyEvaluation

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem comp_reassoc_six {D : Type*} [Category D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : D} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (f₆ : A₅ ⟶ A₆) :
    ((f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ f₅) ≫ f₆ = (f₁ ≫ f₂) ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
  simp

private theorem single_homologyMap (L : CochainComplex C ℤ) (X : C) (c : X ⟶ L.cycles 0) :
    ∃ φ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ L,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        HomologicalComplex.homologyMap φ 0 = c ≫ L.homologyπ 0 := by
  refine ⟨HomologicalComplex.mkHomFromSingle (c ≫ L.iCycles 0) (fun k _ => by simp), ?_⟩
  have h1 : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).homologyπ 0 := by
    rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom]
    simp
  rw [h1, Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0)]
  simp

private theorem exists_cycles (K : DerivedCategory C) :
    ∃ (Z : C) (π : Z ⟶ (DerivedCategory.homologyFunctor C 0).obj K), Epi π ∧
      ∀ (X : C) (c : X ⟶ Z), ∃ x : (DerivedCategory.singleFunctor C 0).obj X ⟶ K,
        (DerivedCategory.homologyFunctor C 0).map x =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X ≫ c ≫ π := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨(DerivedCategory.Q (C := C)).objObjPreimageIso K⟩⟩
  refine ⟨L.cycles 0, L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
    (DerivedCategory.homologyFunctor C 0).map e.hom, ?_, fun X c => ?_⟩
  · have i0 : Epi (L.homologyπ 0) := inferInstance
    have i1 : IsIso ((DerivedCategory.homologyFunctorFactors C 0).inv.app L) :=
      inferInstanceAs (IsIso ((DerivedCategory.homologyFunctorFactors C 0).app L).inv)
    have i2 : Epi ((DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
        (DerivedCategory.homologyFunctor C 0).map e.hom) := epi_comp _ _
    exact @epi_comp _ _ _ _ _ _ i0 _ i2
  obtain ⟨φ, hφ⟩ := single_homologyMap L X c
  refine ⟨(DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
      (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := by
    have h3 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
        (DerivedCategory.homologyFunctor C 0).map (((DerivedCategory.singleFunctorsPostcompQIso C).hom.hom 0).app X) ≫
        𝟙 _ ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := rfl
    have hm : (DerivedCategory.homologyFunctor C 0).map (NatTrans.app (𝟙 ((DerivedCategory.singleFunctors C).functor 0)) X) =
        (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) := rfl
    rw [h3, DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
    erw [Category.id_comp]
    exact congrArg (fun t => t ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) hm
  rw [h2, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  have hφ' : HomologicalComplex.homologyMap φ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom ≫ c ≫ L.homologyπ 0 := by
    rw [← hφ, Iso.hom_inv_id_assoc]
  have n' : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫ HomologicalComplex.homologyMap φ 0) ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app L :=
    (Iso.eq_comp_inv ((DerivedCategory.homologyFunctorFactors C 0).app L)).2
      (DerivedCategory.homologyFunctorFactors_hom_naturality φ 0)
  have key : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctor C 0).map e.hom =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) ≫ c ≫
        L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
          (DerivedCategory.homologyFunctor C 0).map e.hom := by
    rw [n', hφ']
    exact comp_reassoc_six _ _ _ _ _ _
  simpa only [Category.assoc] using key

end UpperTheory.Cb.HomologyEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.HomologyEvaluation
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

variable {B : Scheme.{0}} {q : ℕ}

private def ev (H : SShv B q) (U : B.Etale) :
    ((F0 B q).obj U ⟶ H) ≃ ToType (H.obj.obj (op U)) :=
  ((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H).trans
    ((((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv
      (uliftYoneda.{1}.obj U) H.obj).trans uliftYonedaEquiv)

private theorem ev_comp {H H' : SShv B q} (g : H ⟶ H') (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    ev H' U (t ≫ g) = g.hom.app (op U) (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_right t g
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_right
    (X := uliftYoneda.{1}.obj U) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t) ((sheafToPresheaf _ _).map g)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U) H'.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_comp _ _)

private theorem ev_map (H : SShv B q) {U U' : B.Etale} (a : U' ⟶ U) (t : (F0 B q).obj U ⟶ H) :
    ev H U' ((F0 B q).map a ≫ t) = H.obj.map a.op (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_left
      (X' := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U'))
      (X := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U))
      (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).map
        (uliftYoneda.{1}.map a)) t
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_left
    (uliftYoneda.{1}.map a) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U') H.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_naturality _ a.op).symm

private theorem lift_local {Z H : SShv B q} (π : Z ⟶ H) [Epi π] (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    Cov U (fun U' a => ∃ c : (F0 B q).obj U' ⟶ Z, c ≫ π = (F0 B q).map a ≫ t) := by
  haveI : EssentiallySmall.{1} B.Etale := inferInstance
  haveI : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) := inferInstance
  have hls : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} (ZMod q))) π).2 inferInstance
  refine ⟨Presheaf.imageSieve π.hom (ev H U t),
    Presheaf.imageSieve_mem (EtTop B) π.hom (U := op U) (ev H U t), fun U' a ha => ?_⟩
  obtain ⟨z, hz⟩ := ha
  refine ⟨(ev Z U').symm z, (ev H U').injective ?_⟩
  rw [ev_comp, ev_map, Equiv.apply_symm_apply]
  exact hz

end UpperTheory.Cb.HomologyEvaluation

open UpperTheory.Cb.HomologyEvaluation LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShMapZeroPf.Gen in
theorem UpperTheory.Cb.free_etale_sheaf_lift_exists :
    LateralTheory.E.LeafShMapZeroPf.EtaleLift' := by
  intro B q K U s
  obtain ⟨Z, π, hπ, hlift⟩ := exists_cycles (C := SShv B q) K
  refine (lift_local π U ((e0 B q).inv.app U ≫ s)).mono fun U' a hc => ?_
  obtain ⟨c, hc⟩ := hc
  obtain ⟨x, hx⟩ := hlift _ c
  refine ⟨x, ?_⟩
  have he : (e0 B q).hom.app U' =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0).hom.app ((F0 B q).obj U') :=
    Category.comp_id _
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  have s1 : s = (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by
    rw [Iso.hom_inv_id_app_assoc]
  have h1 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
        (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by rw [← s1]
  have h2 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
      (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s := by
    rw [reassoc_of% n]
    rfl
  have h3 : (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ c ≫ π := by rw [hc]
  have h4 : (e0 B q).hom.app U' ≫ c ≫ π =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x := by
    rw [he]; exact hx.symm
  exact h1.trans (h2.trans (h3.trans h4))
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NeighbourhoodCohomologyObstructionExact
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace UpperTheory.Cb.ConeExactness

private theorem cone_exact (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ)
    (y : HK R (mappingCone φ) F (m + 1))
    (hy : HK.pull R (mappingCone.inr φ) F (m + 1) y = 0) :
    ∃ w, HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) w = y := by
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add (m + 1))) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', β, hβ⟩ := hy
  obtain rfl : m' = m := by omega
  have hβ' : δ m' (m' + 1) β = (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add (m' + 1)) := by
    rw [hβ]; rfl

  let e : Cochain (mappingCone φ) (res R F) m' := (mappingCone.snd φ).comp β (zero_add m')
  let d : Cochain (mappingCone φ) (res R F) (m' + 1) := c.1 - δ m' (m' + 1) e
  have hinre : (Cochain.ofHom (mappingCone.inr φ)).comp e (zero_add m') = β := by
    simp only [e]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_snd]
    simp
  have hinr : (Cochain.ofHom (mappingCone.inr φ)).comp d (zero_add (m' + 1)) = 0 := by
    simp only [d]
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hinre, hβ', sub_self]
  have hdcl : δ (m' + 1) (m' + 1 + 1) d = 0 := by
    simp only [d]
    rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  let a : Cochain K (res R F) m' := (mappingCone.inl φ).comp d (by omega)
  have hdec : (mappingCone.fst φ).1.comp a (add_comm 1 m') = d := by
    have hid := mappingCone.id φ
    have h2 : ((mappingCone.fst φ).1.comp (mappingCone.inl φ) (add_neg_cancel 1) +
        (mappingCone.snd φ).comp (Cochain.ofHom (mappingCone.inr φ)) (add_zero 0)).comp d (zero_add (m' + 1)) = d := by
      rw [hid]; simp
    rw [Cochain.add_comp, Cochain.comp_assoc _ _ _ (add_neg_cancel 1) (show (-1 : ℤ) + (m' + 1) = m' by omega)
        (show (1 : ℤ) + -1 + (m' + 1) = m' + 1 by omega),
      Cochain.comp_assoc_of_second_is_zero_cochain, hinr] at h2
    simpa [a] using h2
  have ha : δ m' (m' + 1) a = 0 := by
    have h1 := δ_comp (mappingCone.fst φ).1 a (add_comm 1 m') 2 (m' + 1) (m' + 1 + 1) rfl (by omega) rfl
    rw [hdec, hdcl, Cocycle.δ_eq_zero] at h1
    have h2 := congrArg (fun t => (mappingCone.inl φ).comp t (show (-1 : ℤ) + (m' + 1 + 1) = m' + 1 by omega)) h1
    simp only [Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero] at h2
    rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (show (1 : ℤ) + (m' + 1) = m' + 1 + 1 by omega)
      (show (-1 : ℤ) + 1 + (m' + 1) = m' + 1 by omega), mappingCone.inl_fst] at h2
    simpa using h2.symm
  refine ⟨CohomologyClass.mk (Cocycle.mk a (m' + 1) rfl ha), ?_⟩
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (Cocycle.mk a (m' + 1) rfl ha) (add_comm 1 m')) =
    CohomologyClass.mk c
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', by omega, -e, ?_⟩
  change _ = (mappingCone.fst φ).1.comp a (add_comm 1 m') - c.1
  rw [hdec, δ_neg]
  simp [d]

end UpperTheory.Cb.ConeExactness

theorem UpperTheory.Cb.neighbourhood_cohomology_obstruction_exact :
    LateralTheory.E.NeighbourhoodKilling.ObsExact := by
  intro q _ U E u i m y hy
  exact UpperTheory.Cb.ConeExactness.cone_exact (ZMod q) _ _ m y hy
end
end

