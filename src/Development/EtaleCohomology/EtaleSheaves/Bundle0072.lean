module

public import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
public import Development.EtaleCohomology.EtaleSheaves.Bundle0042
public import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0055
public import Development.EtaleCohomology.EtaleSheaves.Bundle0067
public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
public import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.EtaleCohomology.EtaleSheaves.Bundle0071
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.TwPairExists
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
public import Development.EtaleCohomology.EtaleSheaves.Bundle0053
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0039
public import Development.EtaleCohomology.EtaleSheaves.Bundle0043
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044
public import Development.EtaleCohomology.EtaleSheaves.Bundle0027
public import Development.EtaleCohomology.TateTwists.Bundle0034
public import Development.EtaleCohomology.TateTwists.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0068
public import Development.EtaleCohomology.EtaleSheaves.Bundle0069
public import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ArchimedeanCokernel
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut
theorem LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of (hD : LateralTheory.E.TruncationKernel.RelDesc) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩
  have hinj := hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
  refine LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)
  refine (LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_
  rw [← hx]
  exact LateralTheory.E.KernelLocalization.bd_pull ..
theorem LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm
  have h := LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  exact ⟨h.2, h.1 (m - 1) (by omega)⟩
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BoundaryKernel
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BridgeYfiPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.Bridge_yfiPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling

structure Sys (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) (u : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  mem : ∀ j, u ∈ Set.range (a j).left
  tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j)
  tr_id : ∀ j, tr (𝟙 j) = 𝟙 (V j)
  tr_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), tr (f ≫ g) = tr g ≫ tr f
  tr_a : ∀ {j k : J} (f : j ⟶ k), tr f ≫ a j = a k
  A : Type
  [ring : CommRing A]
  sh : SH A
  t : Sp A ⟶ U.left
  gY : ∀ j, pullback p (t ≫ U.hom) ⟶ YU p (V j)
  gW : ∀ j, pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι
  sq : ∀ j, prS p ι (t ≫ U.hom) ≫ gY j = gW j ≫ prU p ι (V j)
  gY_a : ∀ j, gY j ≫ resY p (a j) = tY p U t
  gW_a : ∀ j, gW j ≫ resYW p ι (a j) = tW p ι U t
  gY_tr : ∀ {j k : J} (f : j ⟶ k), gY k ≫ resY p (tr f) = gY j
  gW_tr : ∀ {j k : J} (f : j ⟶ k), gW k ≫ resYW p ι (tr f) = gW j
  injY : ∀ j (y : Ht q (sch.obj (YU p (V j))) m i), pull (ZMod q) (sch.map (gY j)) (tw q i) m y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resY p (tr f))) (tw q i) m y = 0
  surY : ∀ y : Ht q (sch.obj (pullback p (t ≫ U.hom))) (m - 1) i,
    ∃ (j : J) (y' : Ht q (sch.obj (YU p (V j))) (m - 1) i), pull (ZMod q) (sch.map (gY j)) (tw q i) (m - 1) y' = y
  injW : ∀ j (w : Ht q (sch.obj (pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι)) (m - 1) i),
    pull (ZMod q) (sch.map (gW j)) (tw q i) (m - 1) w = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resYW p ι (tr f))) (tw q i) (m - 1) w = 0

def Geo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Pack : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
  (u : U.left) (_ : Sys q i p ι U m u) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem Bridge_of_geo_pack (hG : Geo) (hP : Pack) : Bridge := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z u
  obtain ⟨S⟩ := hG hH q k hq i toK ι p hp U m u
  exact hP q i p ι U m u S z

end LateralTheory.E.Bridge_yfiPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartBCNnmPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData LateralTheory.E.ProjectiveLineCharts₂

namespace LateralTheory.E.ChartBC_nnmPf

theorem res_bijective {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  have : (homOfLE h) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

theorem pushout_gen {Z X Y P : CommRingCat.{0}} {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (R : Subring P) (hi : ∀ x, i x ∈ R) (hj : ∀ y, j y ∈ R) (p : P) : p ∈ R := by
  let i' : X ⟶ CommRingCat.of R := CommRingCat.ofHom (i.hom.codRestrict R hi)
  let j' : Y ⟶ CommRingCat.of R := CommRingCat.ofHom (j.hom.codRestrict R hj)
  have w' : f ≫ i' = g ≫ j' := by
    ext z
    have := congrArg (fun φ => φ.hom z) h.w
    simpa [i', j'] using this
  let σ := h.desc i' j' w'
  have hσ : σ ≫ CommRingCat.ofHom R.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc]; ext; rfl
    · rw [h.inr_desc_assoc]; ext; rfl
  have := congrArg (fun φ => φ.hom p) hσ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  rw [← this]; exact (σ.hom p).2

theorem restrict_appTop_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ (f ∣_ U).appTop =
      f.app U ≫ X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).le).op := by
  rw [morphismRestrict_appTop]
  have e := f.naturality (homOfLE (Scheme.Opens.ι_image_top U).le).op
  calc _ = (Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ f.app (U.ι ''ᵁ ⊤)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc, ← Functor.map_comp]; rfl

theorem snd_eq {A : Type} [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (V : L.Opens) :
    (V.ι ≫ l).appTop = l.appLE ⊤ V le_top ≫ L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top V).le).op := by
  unfold Scheme.Hom.appLE
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem ChartBC_of : ChartBC := by
  intro A _ L l f hf W x hW hsx
  have hpb := IsPullback.paste_vert (isPullback_morphismRestrict f W) hf
  have : IsAffine W.toScheme := hW
  have hA : IsAffineOpen (f ⁻¹ᵁ W) := IsAffine.of_isPullback hpb
  refine ⟨hA, ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hA
  have hpo := isPushout_appTop_of_isPullback hpb
  let ψ := L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le).op
  have hψ := res_bijective (X := L) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).ge
  let R : Subring Γ((f ⁻¹ᵁ W).toScheme, ⊤) :=
    (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x)).range.map ψ.hom
  intro t
  have ht : ψ t ∈ R := pushout_gen hpo R ?_ ?_ (ψ t)
  · obtain ⟨r, ⟨q, rfl⟩, hr⟩ := Subring.mem_map.mp ht
    exact ⟨q, hψ.1 hr⟩
  · intro w
    obtain ⟨w0, rfl⟩ := (res_bijective (X := P1) (Scheme.Opens.ι_image_top W).le
      (Scheme.Opens.ι_image_top W).ge).2 w
    have h1 : (f ∣_ W).appTop (P1.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op w0) =
        ψ (f.app W w0) := congrArg (fun φ => φ.hom w0) (restrict_appTop_eq f W)
    erw [h1]
    obtain ⟨q, rfl⟩ := hsx w0
    refine Subring.mem_map.mpr ⟨_, ⟨q.map (Int.castRingHom A), rfl⟩, ?_⟩
    congr 1
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    congr 1; exact RingHom.ext_int _ _
  · intro a
    refine Subring.mem_map.mpr ⟨_, ⟨Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a), rfl⟩, ?_⟩
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, snd_eq]
    simp only [rA, RingHom.comp_apply]
    erw [Iso.hom_inv_id_apply]
    rfl

end LateralTheory.E.ChartBC_nnmPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle
section
namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.H0Lifting
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.H0Lifting
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem exists_epi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (M : DerivedCategory A) :
    ∃ (Z : A) (φ : (DerivedCategory.singleFunctor A 0).obj Z ⟶ M),
      Epi ((DerivedCategory.homologyFunctor A 0).map φ) := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  let φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)
  have h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫
      HomologicalComplex.cyclesMap φ0 0 = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp [φ0]
  have h2 : Epi (HomologicalComplex.cyclesMap φ0 0) := epi_of_epi_fac h1
  have h3 : Epi (HomologicalComplex.homologyMap φ0 0) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)
  have h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0)) := by
    have h := (DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0
    have h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0) := h3
    exact epi_of_epi_fac h.symm
  refine ⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)

theorem transport {A D : Type*} [Category A] [Category D] (S : A ⥤ D) (H : D ⥤ A) (η : S ⋙ H ≅ 𝟭 A)
    {X Y Z : A} {M : D} (a : X ⟶ Y) (s : X ⟶ Z) (t : H.obj (S.obj Y) ⟶ H.obj M) (φ : S.obj Z ⟶ M)
    (h : a ≫ η.inv.app Y ≫ t = s ≫ η.inv.app Z ≫ H.map φ) : H.map (S.map a) ≫ t = H.map (S.map s ≫ φ) := by
  have h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a) := η.inv.naturality a
  have h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s) := η.inv.naturality s
  have h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))
  rw [Functor.map_comp]
  exact (cancel_epi _).1 h3

abbrev PF (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

def gen {B : Scheme.{0}} (q : ℕ) {U V : B.Etale} (a : V ⟶ U) : ((PF B q).obj U).obj (op V) :=
  ModuleCat.freeMk (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem gen_res {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).obj U).map b.op (gen q a) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem gen_map {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).map a).app (op W) (gen q b) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem pf_ext {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (f g : (PF B q).obj U ⟶ F) (h : f.app (op U) (gen q (𝟙 U)) = g.app (op U) (gen q (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
  rintro ⟨a⟩
  change f.app (op V) (gen q a) = g.app (op V) (gen q a)
  have e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U)) := by rw [gen_res, Category.comp_id]
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

theorem pf_exists {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (s : F.obj (op U)) : ∃ f : (PF B q).obj U ⟶ F, f.app (op U) (gen q (𝟙 U)) = s := by
  let c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U))
      (TypeCat.ofHom (fun a => F.map a.down.op s))
  have hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s := fun V a =>
    ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
    refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
    rintro ⟨a⟩
    change c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))
    rw [gen_res, hc, hc, op_comp, Functor.map_comp]
    rfl
  · change c (op U) _ = _
    rw [hc]
    simp

theorem loc_lift {B : Scheme.{0}} {q : ℕ} {F G : SShv B q} (π : F ⟶ G) [Epi π] (U : B.Etale)
    (t : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U) ⟶ G) :
    Cov U (fun U' a => ∃ s : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U') ⟶ F,
      (presheafToSheaf (EtTop B) _).map ((PF B q).map a) ≫ t = s ≫ π) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  have hπ : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  let adj := sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let t' : (PF B q).obj U ⟶ G.obj := adj.homEquiv _ _ t
  refine ⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩
  rintro U' a ⟨z, hz⟩
  obtain ⟨f, hf⟩ := pf_exists (F := F.obj) z
  refine ⟨(adj.homEquiv _ F).symm f, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply pf_ext
  change t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))
  rw [hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]

theorem etale_sheaf_epi_lifts_degree_zero_derived_maps_locally : EtaleDerivedDegreeZeroHomologyLocallyLifts := by
  intro B q M U t
  obtain ⟨Z, φ, hφ⟩ := exists_epi M
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0
  let X : B.Etale ⥤ SShv B q := PF B q ⋙ presheafToSheaf (EtTop B) _
  let π : Z ⟶ (H0 B q).obj M := η.inv.app Z ≫ (H0 B q).map φ
  have hπ : Epi π := epi_comp _ _
  let t0 : X.obj U ⟶ (H0 B q).obj M := η.inv.app (X.obj U) ≫ t
  refine (loc_lift π U t0).mono ?_
  rintro U' a ⟨s, hs⟩
  refine ⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩
  exact transport _ _ η (X.map a) s t φ hs

end LateralTheory.E.H0Lifting
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KerLocOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedSH0Of
section
namespace LateralTheory.E.LeafClosedSH0PfCut
open LateralTheory.E.LeafClosedSH0Pf

theorem LeafClosedSH0_of (hS : LeafSHSieve) : LateralTheory.E.LeafVanBPf.LeafClosedSH0 :=
  LateralTheory.E.LeafClosedSH0Pf.LeafClosedSH0_of hS LateralTheory.E.LeafClosedSH0PfQuot.shQuot
    LateralTheory.E.LeafClosedSH0PfEmpty.emptySec LateralTheory.E.LeafClosedSH0PfPrim.primLift

end LateralTheory.E.LeafClosedSH0PfCut
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNSysGlueOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodSystemGluing
open LateralTheory.E.LeafSHSysPf

theorem cocone_u_eq {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j')
    (c : Cocone D) (j j' : J) : u j ≫ c.ι.app j = u j' ≫ c.ι.app j' := by
  have h1 := c.w (IsFiltered.leftToMax j j')
  have h2 := c.w (IsFiltered.rightToMax j j')
  rw [← h1, ← h2, ← Category.assoc, ← Category.assoc, hu, hu]

theorem LeafNSysGlue_of (hR : LeafRingSys) : LeafNSysGlue := by
  intro _ B U x
  let 𝒰 := U.left.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let ι : Spec R ⟶ U.left := 𝒰.f (𝒰.idx x)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨J, _, _, D, u, hu, het, hq, c, ⟨hc⟩, hcof⟩ := hR R y
  have hE : ∀ j, Etale (Spec.map (u j) ≫ ι ≫ U.hom) := fun j => by
    have : Etale (Spec.map (u j)) := HasRingHomProperty.Spec_iff.2 (het j)
    have : Etale U.hom := U.prop
    infer_instance
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (Spec.map (u j) ≫ ι ≫ U.hom) (hE j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (u j) ≫ ι) (by show (Spec.map (u j) ≫ ι) ≫ U.hom = Spec.map (u j) ≫ ι ≫ U.hom; rw [Category.assoc]) trivial
  let tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j := fun {j j'} g =>
    MorphismProperty.Over.homMk (Spec.map (D.map g))
      (by show Spec.map (D.map g) ≫ Spec.map (u j) ≫ ι ≫ U.hom = Spec.map (u j') ≫ ι ≫ U.hom; rw [← Spec.map_comp_assoc, hu]) trivial
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  exact ⟨{
    J := J
    D := D
    V := V
    a := a
    e := fun j => Iso.refl _
    tr := tr
    tr_a := fun g => by
      apply MorphismProperty.Over.Hom.ext
      show Spec.map (D.map g) ≫ Spec.map _ ≫ ι = Spec.map _ ≫ ι
      rw [← Spec.map_comp_assoc, hu]
    tr_spec := fun g => by
      show 𝟙 _ ≫ Spec.map (D.map g) ≫ 𝟙 _ = _
      simp
    hx := fun j => by
      obtain ⟨q, hq⟩ := hq j
      refine ⟨q, ?_⟩
      rw [← hy]
      show ι (Spec.map (u j) q) = ι y
      congr 1
    c := c
    hc := hc
    cof := hcof
    t := Spec.map (c.ι.app j0) ≫ Spec.map (u j0) ≫ ι
    ht := fun j => by
      show _ = Spec.map (c.ι.app j) ≫ 𝟙 _ ≫ Spec.map (u j) ≫ ι
      rw [Category.id_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cocone_u_eq D u hu c j0 j] }⟩

end LateralTheory.E.NeighbourhoodSystemGluing
end
end

