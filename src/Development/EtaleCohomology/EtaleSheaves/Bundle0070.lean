module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
public import Development.EtaleCohomology.EtaleSheaves.Bundle0065
public import Development.EtaleCohomology.EtaleSheaves.Bundle0062
public import Development.EtaleCohomology.EtaleSheaves.Bundle0064
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
public import Development.EtaleCohomology.EtaleSheaves.Bundle0023

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafProjModelPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.LeafProjModelPf

theorem image_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have hB := Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing
  have hred : ∀ U : Y.affineOpens, _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) := fun U =>
    isReduced_of_injective _ (f.toImage_app_injective U)
  refine @isReduced_of_isReduced_stalk _ (fun z => ⟨?_⟩)
  rintro g ⟨n, e⟩
  obtain ⟨U, hzU, s, rfl⟩ := f.image.presheaf.exists_germ_eq g
  rw [← map_pow, ← map_zero (f.image.presheaf.germ _ z hzU).hom] at e
  obtain ⟨V, hzV, iU, iV, e'⟩ := f.image.presheaf.germ_eq z hzU hzU _ 0 e
  rw [map_pow, map_zero] at e'
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hzV
  have h0 : f.image.presheaf.map (homOfLE hWV).op (f.image.presheaf.map iU.op s) = 0 := by
    have hx := congrArg (f.image.presheaf.map (homOfLE hWV).op) e'
    rw [map_pow, map_zero] at hx
    exact (hred ⟨W, hW⟩).eq_zero _ ⟨n, hx⟩
  rw [← f.image.presheaf.germ_res iU z hzV, ← f.image.presheaf.germ_res (homOfLE hWV) z hzW]
  simp only [CommRingCat.comp_apply] at h0 ⊢
  rw [h0, map_zero]

theorem image_irreducible {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IrreducibleSpace X] :
    IrreducibleSpace f.image := by
  have h1 : IsIrreducible (Set.range f.toImage) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
  have h2 := h1.closure
  rw [f.toImage.denseRange.closure_range] at h2
  exact (irreducibleSpace_def _).mpr h2

theorem leafImageIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] (hX : IsIntegral X) :
    IsIntegral f.image := by
  have := image_isReduced f
  have := image_irreducible f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def LeafQProjImm : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (N : ℕ) (φ : Spec (CommRingCat.of A) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace k N),
    IsImmersion φ ∧ QuasiCompact φ ∧
    φ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N = Spec.map (CommRingCat.ofHom (algebraMap k A))

theorem LeafProjModel_of (h1 : LeafQProjImm) : LateralTheory.E.LeafCloseBCut.LeafProjModel := by
  intro k _ A _ _ _ _
  obtain ⟨N, φ, hi, hq, hc⟩ := h1 k A
  refine ⟨φ.image, φ.imageι ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N, φ.toImage, leafImageIntegral φ inferInstance,
    ?_, inferInstance, ?_⟩
  · have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
    infer_instance
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact hc

end LateralTheory.E.LeafProjModelPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPtVPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafPtVPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling
  LateralTheory.E.SecondDegreeKilling.Comp LateralTheory.E.SecondDegreeKilling.Nbhd

theorem isZero_sec_empty (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    IsZero (F.obj.obj (op X)) :=
  (Sheaf.isTerminalOfBotCover F X (Scheme.bot_mem_grothendieckTopology (P := @Etale) X)).isZero

theorem isZero_free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext1
  ext1 U
  by_cases hU : IsEmpty U.unop
  · exact (isZero_sec_empty R ((free R).obj (yoneda.obj X)) U.unop).eq_of_tgt _ _
  · have hE : IsEmpty (ULift.{1} (unop U ⟶ X)) := ⟨fun f => by
      obtain ⟨x⟩ := not_isEmpty_iff.1 hU; exact IsEmpty.false (f.down.base x)⟩
    haveI : Subsingleton ↑(((freeP R).obj (yoneda.obj X)).obj U) := by
      change Subsingleton (ULift.{1} (unop U ⟶ X) →₀ ULift.{1} R); infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

theorem isZero_chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases p with _ | k
    · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) 0)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro j; change -(j : ℤ) ≠ (k : ℤ) + 1; omega)
  · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) p)

theorem isIso_inr (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (hK : ∀ n, IsZero (K.X n)) :
    IsIso (mappingCone.inr φ) := by
  have : ∀ p, IsIso ((mappingCone.inr φ).f p) := fun p => ⟨⟨(mappingCone.snd φ).v p p (add_zero p), by simp, by
    rw [← mappingCone.id_X φ p (p + 1) rfl, (hK (p + 1)).eq_of_tgt ((mappingCone.fst φ).1.v p (p + 1) rfl) 0]
    simp⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem fgt_bij (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} [IsEmpty X] {E : Spc}
    (f : sch.obj X ⟶ E) (n : ℤ) : Function.Bijective (fgt R f F n) := by
  haveI := isIso_inr R ((chains R).map f) (isZero_chains_empty R X)
  exact hH.1 R (mappingCone.inr ((chains R).map f)) F n

theorem rpl_zero (hH : Hyps) (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') [IsEmpty U']
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (he : pl q i e n = 0)
    (x : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f' u e comm n x = 0 := by
  apply (fgt_bij hH (ZMod q) (tw q i) (sch.map f') n).1
  rw [map_zero]
  refine (relNat (ZMod q) (tw q i) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) n x).trans ?_
  change pl q i e n _ = 0
  rw [he]; rfl

theorem isEmpty_pullback_closed_subscheme_section_into_complement {B W Y S : Scheme.{0}} (ι : W ⟶ B) (V : B.Opens) (hVW : (V : Set B) = (Set.range ι)ᶜ)
    (p : Y ⟶ B) (s : S ⟶ B) (hs : Set.range ⇑s ⊆ (V : Set B)) :
    IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun x => by
  have h1 : (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s ≫ s) x = (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x := by
    rw [pullback.condition]
  have h2 : (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x ∈ (V : Set B) := by
    rw [← h1]; apply hs; simp only [Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  rw [hVW] at h2; simp only [Scheme.Hom.comp_apply] at h2; exact h2 ⟨_, rfl⟩⟩

theorem LeafPtV_of : LateralTheory.E.SecondDegreeKilling.LeafPtV := by
  intro hH q _ k _ hq i B W Y Y' toK ι _ V hVW p g hp hgp U A _ t hA hV m hpl y
  haveI := isEmpty_pullback_closed_subscheme_section_into_complement ι V hVW (g ≫ p) (t ≫ U.hom) hV
  let wA : pullback (pullback.snd (g ≫ p) (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶
      pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι :=
    pullback.map _ ι _ ι (fibMap g p (t ≫ U.hom)) (𝟙 W) (𝟙 B)
      (by rw [Category.comp_id, ← Category.assoc (fibMap g p (t ≫ U.hom)), pullback.lift_snd, Category.comp_id]) (by simp)
  have commA : prS (g ≫ p) ι (t ≫ U.hom) ≫ fibMap g p (t ≫ U.hom) = wA ≫ prS p ι (t ≫ U.hom) :=
    (pullback.lift_fst _ _ _).symm
  have hA : prS p ι (t ≫ U.hom) ≫ tY p U t = tW p ι U t ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have hB : prS (g ≫ p) ι (t ≫ U.hom) ≫ tY (g ≫ p) U t = tW (g ≫ p) ι U t ≫ prU (g ≫ p) ι U :=
    (pullback.lift_fst _ _ _).symm
  have hC : prU (g ≫ p) ι U ≫ mY p g U = mW p g ι U ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have E1 : tY (g ≫ p) U t ≫ mY p g U = fibMap g p (t ≫ U.hom) ≫ tY p U t := by
    simp only [tY, mY, fibMap, pullback.map_comp, Category.id_comp, Category.comp_id]
  have c1 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (tY (g ≫ p) U t ≫ mY p g U) =
      (tW (g ≫ p) ι U t ≫ mW p g ι U) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mY p g U) hB).trans ((Category.assoc _ _ _).trans
      ((congrArg (tW (g ≫ p) ι U t ≫ ·) hC).trans (Category.assoc _ _ _).symm)))
  have c2 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (fibMap g p (t ≫ U.hom) ≫ tY p U t) =
      (wA ≫ tW p ι U t) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ tY p U t) commA).trans ((Category.assoc _ _ _).trans
      ((congrArg (wA ≫ ·) hA).trans (Category.assoc _ _ _).symm)))
  have E2 : tW (g ≫ p) ι U t ≫ mW p g ι U = wA ≫ tW p ι U t := by
    simp only [tW, mW, wA, pullback.map_comp]
    congr 1
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ c1, rpl_congr q i _ _ _ _ _ _ c1 c2 E2 E1, ← rpl_comp q i _ _ _ _ _ hA _ _ commA c2]
  exact rpl_zero hH q i _ _ _ _ commA m hpl _

end LateralTheory.E.LeafPtVPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHPtPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf

theorem germ (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B : Scheme.{0}} (U : B.Etale) (x : U.left)
    {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (he : ∀ j, IsIso (e j)) (hy : ∀ j, (a j).left (y j) = x)
    (hq : ∀ j, IsUnit ((q : ℕ) : D.obj j))
    (hcomp : ∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left)
    (ht : ∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t)
    (s : Sec (tw q i) U.left) (hs : Sec.res t s = 0) :
    ∃ (U' : B.Etale) (a' : U' ⟶ U) (y' : U'.left), a'.left y' = x ∧ Sec.res a'.left s = 0 := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  have hB1 : B1 := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, eq, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  set z : Ht q (sp (D.obj j)) 0 i := eq _ (Sec.res (e j ≫ (a j).left) s) with hz
  have h0 : pull _ (spMap (c.ι.app j).hom) _ _ z = 0 := by
    rw [hz, spMap, hnat, ← res_comp, ht, hs, map_zero]
  obtain ⟨k, f, hk⟩ := (hB1 q D c hc 0 i).2 j z (hq j) h0
  rw [hz, spMap, hnat, ← res_comp, hcomp] at hk
  have hk' : Sec.res (e k ≫ (a k).left) s = 0 := (eq _).injective (by rw [hk, map_zero])
  refine ⟨V k, a k, y k, hy k, ?_⟩
  have := congrArg (Sec.res (inv (e k))) hk'
  rw [← res_comp, IsIso.inv_hom_id_assoc] at this
  simpa using this

def LeafSHNb : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left), (∀ j, IsIso (e j)) ∧ (∀ j, (a j).left (y j) = x) ∧ (∀ j, IsUnit ((q : ℕ) : D.obj j)) ∧
    (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
    (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧ SH c.pt ∧
    (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left)

def LeafSHTop : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) {J : Type} [SmallCategory J] [Nonempty J]
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
  (t : Sp c.pt ⟶ U.left), (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) →
  (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left) →
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a' : U' ⟶ U), S a' ∧ ∃ t' : Sp c.pt ⟶ U'.left, t' ≫ a'.left = t)

theorem LeafSHPt_of (hN : LeafSHNb) (hT : LeafSHTop) : LeafSHPt := by
  intro hH q _ k _ hq i B U s0 x
  obtain ⟨J, _, _, D, c, hc, V, a, y, e, t, he, hy, hqj, hcomp, ht, hSH, hcof⟩ := hN hH q k hq U s0 x
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨hO, hL⟩ := hT U x D c V a e t ht hcof
  exact ⟨c.pt, inferInstance, t, hSH, hO, hL, fun s hs => germ hH q i U x D c hc V a y e t he hy hqj hcomp ht s hs⟩

end LateralTheory.E.LeafSHPtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTripleFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafTripleFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem pb_lift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {f : D ⟶ Sp R} {v : C ⟶ D} (hs : IsPullback v c f (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w)) c
      (pullback.snd f (incl h)) (toR R') := by
  have e1 : pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ pullback.fst f (incl h) = v :=
    pullback.lift_fst _ _ _
  have t : IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫
      pullback.fst f (incl h)) c f (toR R' ≫ incl h) := by rw [e1, toR_incl]; exact hs
  exact IsPullback.of_right t (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (incl h))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def LeafPairRel : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → ∀ (hs : IsPullback v0 c0 q (toR R)),
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (E1 : Scheme.{0}) (e1 : E1 ⟶ pullback q (incl h)) (w1 : C1 ⟶ E1),
      FP (e1 ≫ pullback.snd q (incl h)) ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ pullback.snd q (incl h)) (toR R') ∧
      γ1 ≫ pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) = w1 ≫ e1

theorem tripleDescent_of_pairRelation (hR : LeafPairRel) : LeafTripleFP := by
  intro k _ Ω _ _ R hRfg C0 C1 C2 c0 γ1 γ2 h2 D0 D1 q d1 v0 v1 hq hq1 hs0 hs1 hc
  obtain ⟨R', h, hR', E2, e2, w2, hf2, hs2, hc2⟩ :=
    hR k Ω R hRfg (γ1 ≫ c0) γ2 h2 (d1 ≫ q) v1 hq1 hs1
  have hsnd : pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]) ≫
      pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR', _, _, _, pullback.snd q (incl h),
    pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]), e2,
    pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs0.w),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs1.w), w2, ?_⟩
  refine ⟨fp_snd _ _ hq, ?_, ?_, pb_lift h hs0, ?_, ?_, ?_, hc2⟩
  · rw [hsnd]; exact fp_snd _ _ hq1
  · rw [hsnd]; exact hf2
  · rw [hsnd]; exact pb_lift h hs1
  · rw [hsnd]; exact hs2
  · apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]

end LateralTheory.E.LeafTripleFPPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPf

def LeafTw0LocGen : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec (tw q 0) U),
  Loc U fun V g => ∃ (e : Sec (tw q 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧ (e = 0 ∨ ∃ ζ : Prim q Γ(V, ⊤), e = twGen 0 ζ)

theorem baerU (q : ℕ) [NeZero q] : Module.Baer (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) := by
  intro I g
  let J : Ideal (ZMod q) :=
    { carrier := {y | (ULift.up y : ULift.{1} (ZMod q)) ∈ I}
      add_mem' := fun {a b} ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c {y} hy => by
        have := I.smul_mem (ULift.up c) hy
        exact this }
  let g' : J →ₗ[ZMod q] ZMod q :=
    { toFun := fun y => (g ⟨ULift.up y.1, y.2⟩).down
      map_add' := fun a b => by
        have := g.map_add ⟨ULift.up a.1, a.2⟩ ⟨ULift.up b.1, b.2⟩
        exact congrArg ULift.down this
      map_smul' := fun c a => by
        have := g.map_smul (ULift.up c) ⟨ULift.up a.1, a.2⟩
        exact congrArg ULift.down this }
  obtain ⟨h, hh⟩ := KStar.Selmer.zmod_baer J g'
  refine ⟨{ toFun := fun x => ULift.up (h x.down)
            map_add' := fun a b => congrArg ULift.up (h.map_add a.down b.down)
            map_smul' := fun c a => congrArg ULift.up (h.map_smul c.down a.down) }, ?_⟩
  intro x hx
  exact congrArg ULift.up (hh x.down hx)

theorem retract (q : ℕ) [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M)
    (hx : ∀ c : ULift.{1} (ZMod q), c • x = 0 → c = 0) :
    ∃ r : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r x = 1 := by
  let f : ULift.{1} (ZMod q) →ₗ[ULift.{1} (ZMod q)] M := LinearMap.toSpanSingleton _ _ x
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc; exact hx c hc
  obtain ⟨r, hr⟩ := (baerU q).extension_property f hf LinearMap.id
  refine ⟨r, ?_⟩
  have := LinearMap.congr_fun hr 1
  simpa [f] using this

def LeafTw0GenFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • resGen 0 ζ = 0 → c = 0

theorem genSplit_of (hF : LeafTw0GenFree) (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) :
    twGen 0 ζ = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r (resGen 0 ζ) = 1 := by
  rcases hF q V ζ with h | h
  · exact Or.inl h
  · exact Or.inr (retract q _ h)

section
variable {R : Type} [CommRing R]

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem map_res' {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  exact congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)
end

theorem LeafTw0LocSplit_of (h1 : LeafTw0LocGen) (h2 : LeafTw0GenFree) : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := by
  intro q _ U n a
  let I : (sgl (tw q 0)).X 0 ≅ tw q 0 := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q 0)
  obtain ⟨S, hS, hP⟩ := h1 q U n (fun k => Sec.map I.hom (a k))
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨e', c, hc, he'⟩ := hP V g hg
  have back : ∀ y : Sec ((sgl (tw q 0)).X 0) V, Sec.map I.inv (Sec.map I.hom y) = y := by
    intro y; refine (map_comp' I.hom I.inv y).symm.trans ?_; simp [Sec.map]
  refine ⟨Sec.map I.inv e', c, fun k => ?_, ?_⟩
  · rw [← back (Sec.res g (a k)), map_res' I.hom g (a k), hc k]
    exact map_smul (I.inv.hom.app (op V)).hom (c k) e'
  · rcases he' with rfl | ⟨ζ, rfl⟩
    · left; simp [Sec.map]
    · rcases genSplit_of h2 q V ζ with h0 | ⟨r, hr⟩
      · left; simp [h0, Sec.map]
      · right; refine ⟨r, ?_⟩
        convert hr using 2
        exact (map_comp' I.inv ((resAug (tw q 0)).f 0) (twGen 0 ζ)).symm

end LateralTheory.E.LeafTw0LocSplitPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPfC
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LocSecPfC

variable (R : Type) [CommRing R] (X : Scheme.{0})

def eqv (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃ Sec G X :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ G).trans <|
  (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv (yoneda.obj X ⋙ uliftFunctor.{1}) G.obj).trans
  (uliftYonedaEquiv.{1} (X := X) (F := G.obj ⋙ forget _))

theorem eqv_apply (G : Shv R) (f : (free R).obj (yoneda.obj X) ⟶ G) :
    eqv R X G f = (f.hom.app (op X)).hom (freeGen R _ X (𝟙 X)) := by
  rfl

def eqvAdd (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X :=
  { eqv R X G with
    map_add' := fun f g => by
      change eqv R X G (f + g) = eqv R X G f + eqv R X G g
      rw [eqv_apply, eqv_apply, eqv_apply]
      rfl }

theorem homSec : LateralTheory.E.LocSecPfB.HomSec := by
  intro R _ X
  refine ⟨eqvAdd R X, fun φ f => ?_⟩
  change eqv R X _ (f ≫ φ) = Sec.map φ (eqv R X _ f)
  rw [eqv_apply, eqv_apply]
  rfl

theorem LocSec_of (h2 : LateralTheory.E.LocSecPfB.ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPfB.LocSec_of homSec h2

end LateralTheory.E.LocSecPfC
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd

structure Tri (J : Type) [SmallCategory J] where
  Rm : J ⥤ AddCommGrpCat.{1}
  Ym : J ⥤ AddCommGrpCat.{1}
  Yp : J ⥤ AddCommGrpCat.{1}
  Wp : J ⥤ AddCommGrpCat.{1}
  cR : Cocone Rm
  cYm : Cocone Ym
  cYp : Cocone Yp
  cWp : Cocone Wp
  fg : Rm ⟶ Ym
  fgL : cR.pt ⟶ cYm.pt
  fg_w : ∀ j, cR.ι.app j ≫ fgL = fg.app j ≫ cYm.ι.app j
  dl : Wp ⟶ Rm
  dlL : cWp.pt ⟶ cR.pt
  dl_w : ∀ j, cWp.ι.app j ≫ dlL = dl.app j ≫ cR.ι.app j
  rs : Yp ⟶ Wp
  rsL : cYp.pt ⟶ cWp.pt
  rs_w : ∀ j, cYp.ι.app j ≫ rsL = rs.app j ≫ cWp.ι.app j

  exR : ∀ j (x : Rm.obj j), (fg.app j).hom x = 0 → ∃ w, (dl.app j).hom w = x

  exWL : ∀ w : cWp.pt, dlL.hom w = 0 → ∃ y, rsL.hom y = w

  cx : ∀ j (y : Yp.obj j), (dl.app j).hom ((rs.app j).hom y) = 0

  injYm : ∀ j (y : Ym.obj j), (cYm.ι.app j).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (Ym.map f).hom y = 0

  surYp : ∀ y : cYp.pt, ∃ (j : J) (y' : Yp.obj j), (cYp.ι.app j).hom y' = y

  injWp : ∀ j (w : Wp.obj j), (cWp.ι.app j).hom w = 0 → ∃ (k : J) (f : j ⟶ k), (Wp.map f).hom w = 0

def PairFive : Prop := ∀ (J : Type) [SmallCategory J] [IsFiltered J] (T : Tri J) (j : J) (x : T.Rm.obj j),
  (T.cR.ι.app j).hom x = 0 → ∃ (k : J) (f : j ⟶ k), (T.Rm.map f).hom x = 0

def ObsExact : Prop := ∀ (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) (y : Hrel (ZMod q) u (tw q i) (m + 1)),
  fgt (ZMod q) u (tw q i) (m + 1) y = 0 → ∃ w, LateralTheory.E.GlueRelPf.obs q u i m w = y

def ObsNat : Prop := ∀ (q : ℕ) [NeZero q] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
  (comm : f' ≫ e = u ≫ f) (i m : ℤ) (w : Ht q U m i),
  rpull (ZMod q) f f' u e comm (tw q i) (m + 1) (LateralTheory.E.GlueRelPf.obs q f i m w) =
    LateralTheory.E.GlueRelPf.obs q f' i m (pull (ZMod q) u (tw q i) m w)

def Bridge : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m) (u : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem goal_of (hF : PairFive) (_hO : ObsExact) (_hN : ObsNat) (hB : Bridge) : LeafKillNbhd := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z hz u
  obtain ⟨J, _, _, T, j0, x0, A, _, t, hSH, hlim, hst⟩ := hB hH q k hq i toK ι p hp U m z u
  obtain ⟨j, f, hf⟩ := hF J T j0 x0 (hlim (hz A t hSH))
  exact hst j f hf

end LateralTheory.E.NeighbourhoodKilling
end
end

