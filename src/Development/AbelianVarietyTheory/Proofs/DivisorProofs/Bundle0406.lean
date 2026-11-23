module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUnivers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitaryOfLocallyBijectiveFromFilteredFunctor
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma etale_inr {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_inr {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eta_map {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma map_comp_apply (N : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {A B C : CommRingCat.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A) :
    (N.map (f ≫ g)).hom x = (N.map g).hom ((N.map f).hom x) := by
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma isPushout_pushouts {C : Type*} [Category C] {A C₁ C₂ X B₁ B₂ P Q : C} {u₁ : A ⟶ C₁}
    {u₂ : A ⟶ C₂} {f : A ⟶ X} {i₁ : C₁ ⟶ B₁} {g₁ : X ⟶ B₁} {i₂ : C₂ ⟶ B₂} {g₂ : X ⟶ B₂}
    {p₁ : C₁ ⟶ P} {p₂ : C₂ ⟶ P} {q₁ : B₁ ⟶ Q} {q₂ : B₂ ⟶ Q} {w : P ⟶ Q}
    (h₁ : IsPushout u₁ f i₁ g₁) (h₂ : IsPushout u₂ f i₂ g₂) (hP : IsPushout u₁ u₂ p₁ p₂)
    (hQ : IsPushout g₁ g₂ q₁ q₂) (e₁ : p₁ ≫ w = i₁ ≫ q₁) (e₂ : p₂ ≫ w = i₂ ≫ q₂) :
    IsPushout (u₁ ≫ p₁) f w (g₁ ≫ q₁) := by
  have s : IsPushout u₂ (u₁ ≫ i₁) (p₂ ≫ w) q₁ := by
    rw [h₁.w, e₂]; exact h₂.paste_vert hQ.flip
  have t : IsPushout p₁ i₁ w q₁ := IsPushout.of_top s e₁ hP.flip
  exact h₁.paste_horiz t

lemma glue (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (s : ∀ i, (onRings F).obj (C i))
    (hs : ∀ a b, ((onRings F).map (pushout.inl (e a) (e b))).hom (s a) =
      ((onRings F).map (pushout.inr (e a) (e b))).hom (s b)) :
    ∃ y : (onRings F).obj A, ∀ i, ((onRings F).map (e i)).hom y = s i := by
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).2 s ?_
  intro a b
  have H := isPullback_SpecMap_pushout (e a) (e b)
  have h1 : pullback.fst (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inl (e a) (e b)) := by simp
  have h2 : pullback.snd (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inr (e a) (e b)) := by simp
  have := congrArg (fun z => (F.obj.map H.isoPullback.inv.op).hom z) (hs a b)
  simp only [Sec.res, h1, h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact this

lemma sep (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (y z : (onRings F).obj A)
    (h : ∀ i, ((onRings F).map (e i)).hom y = ((onRings F).map (e i)).hom z) : y = z := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).1 _ ?_
  intro i
  change ((onRings F).map (e i)).hom (y - z) = 0
  rw [map_sub, h i, sub_self]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma cocone_nat {C : Type} [Category C] {D' : C ⥤ CommRingCat.{0}} {B : CommRingCat.{0}}
    (ιB : D' ⟶ (Functor.const C).obj B) {K K' : C} (φ : K ⟶ K') :
    D'.map φ ≫ ιB.app K' = ιB.app K := by
  simpa using ιB.naturality φ

lemma po_stage {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {j : J} {B' : CommRingCat.{0}}
    {g' : D.obj j ⟶ B'} {D' : Under j ⥤ CommRingCat.{0}} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (hpo : ∀ k, IsPushout g' (D.map k.hom) (v.app k) (u.app k))
    {K K' : Under j} (φ : K ⟶ K') :
    IsPushout (u.app K) (D.map φ.right) (D'.map φ) (u.app K') := by
  have hv : v.app K ≫ D'.map φ = v.app K' := by simpa using (v.naturality φ).symm
  have e1 : D.map K.hom ≫ D.map φ.right = D.map K'.hom := by rw [← Functor.map_comp, Under.w φ]
  have s : IsPushout g' (D.map K.hom ≫ D.map φ.right) (v.app K ≫ D'.map φ) (u.app K') := by
    rw [e1, hv]; exact hpo K'
  exact IsPushout.of_top s (u.naturality φ).symm (hpo K)

lemma po_colim {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D} {j : J}
    {B' B : CommRingCat.{0}} {g' : D.obj j ⟶ B'} {h : B' ⟶ B} {g : c.pt ⟶ B}
    (hbig : IsPushout g' (c.ι.app j) h g) {D' : Under j ⥤ CommRingCat.{0}}
    {ιB : D' ⟶ (Functor.const _).obj B} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (k : Under j)
    (hk : IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ιB.app k = h ∧
      u.app k ≫ ιB.app k = c.ι.app k.right ≫ g) :
    IsPushout (u.app k) (c.ι.app k.right) (ιB.app k) g := by
  have e1 : D.map k.hom ≫ c.ι.app k.right = c.ι.app j := c.w k.hom
  rw [← e1, ← hk.2.1] at hbig
  exact IsPushout.of_top hbig hk.2.2 hk.1

theorem surj (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F)
    (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hloc : ∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x)
    (hinj : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (x : (onRings F).obj c.pt) :
    ∃ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = x := by
  classical
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ x
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j0
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hlift : ∀ i, ∃ k : Under j, ∃ n : M.obj ((D' i).obj k), (M.map ((ιB i).app k)).hom n = m i :=
    fun i => (hMel (Under j) (D' i) _ (hcol i).some).1 (m i)
  choose k n hn using hlift
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  let s : ∀ i, (onRings F).obj ((D' i).obj K) :=
    fun i => (η.app _).hom ((M.map ((D' i).map (e i))).hom (n i))
  have hs : ∀ i, ((onRings F).map ((ιB i).app K)).hom (s i) = ((onRings F).map (g i)).hom x := by
    intro i
    simp only [s]
    rw [eta_map, ← map_comp_apply, cocone_nat, hn]
    exact hm i
  let Kp : Under K.right → Under j := fun L => Under.mk (K.hom ≫ L.hom)
  let φ : ∀ L : Under K.right, K ⟶ Kp L := fun L => Under.homMk L.hom
  let s' : ∀ (L : Under K.right) i, (onRings F).obj ((D' i).obj (Kp L)) :=
    fun L i => ((onRings F).map ((D' i).map (φ L))).hom (s i)
  have hover : ∀ a b : ι, ∃ L0 : Under K.right, ∀ (L : Under K.right) (_ : L0 ⟶ L),
      ((onRings F).map (pushout.inl ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L a) =
      ((onRings F).map (pushout.inr ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L b) := by
    intro a b
    let w : pushout ((u a).app K) ((u b).app K) ⟶ pushout (g a) (g b) :=
      pushout.desc ((ιB a).app K ≫ pushout.inl (g a) (g b)) ((ιB b).app K ≫ pushout.inr (g a) (g b))
        (by
          have hua : ∀ i, (u i).app K ≫ (ιB i).app K = c.ι.app K.right ≫ g i := fun i => (hpush i K).2.2
          rw [reassoc_of% (hua a), reassoc_of% (hua b)]
          exact (Category.assoc _ _ _).trans ((c.ι.app K.right ≫= pushout.condition).trans
            (Category.assoc _ _ _).symm))
    let t : (onRings F).obj (pushout ((u a).app K) ((u b).app K)) :=
      ((onRings F).map (pushout.inl _ _)).hom (s a) - ((onRings F).map (pushout.inr _ _)).hom (s b)
    have ht : ((onRings F).map w).hom t = 0 := by
      simp only [t, map_sub, ← map_comp_apply, w, pushout.inl_desc, pushout.inr_desc]
      rw [map_comp_apply _ ((ιB a).app K), map_comp_apply _ ((ιB b).app K), hs, hs,
        ← map_comp_apply, ← map_comp_apply, pushout.condition, sub_self]
    have hPO : IsPushout ((u a).app K ≫ pushout.inl _ _) (c.ι.app K.right) w
        (g a ≫ pushout.inl (g a) (g b)) :=
      isPushout_pushouts (po_colim (hsq a).2 K (hpush a K)) (po_colim (hsq b).2 K (hpush b K))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    obtain ⟨D'', ι'', u'', v'', hcol'', hpush''⟩ :=
      GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc K.right _ _ _ w _ hPO
    let k0 : Under K.right := Under.mk (𝟙 _)
    have h0 : ((onRings F).map (ι''.app k0)).hom (((onRings F).map (v''.app k0)).hom t) = 0 := by
      rw [← map_comp_apply, (hpush'' k0).2.1, ht]
    obtain ⟨L0, f, hf⟩ := hinj (Under K.right) D'' _ hcol''.some k0 _ h0
    refine ⟨L0, fun L ψ => ?_⟩
    have hvL : ((onRings F).map (v''.app L)).hom t = 0 := by
      have e1 : v''.app k0 ≫ D''.map f ≫ D''.map ψ = v''.app L := by
        rw [← D''.map_comp]
        simpa using (v''.naturality (f ≫ ψ)).symm
      rw [← e1, map_comp_apply, map_comp_apply, hf, map_zero]
    let w' : pushout ((u a).app K) ((u b).app K) ⟶ pushout ((u a).app (Kp L)) ((u b).app (Kp L)) :=
      pushout.desc ((D' a).map (φ L) ≫ pushout.inl _ _) ((D' b).map (φ L) ≫ pushout.inr _ _)
        (by
          rw [← Category.assoc, ← Category.assoc, ← (u a).naturality, ← (u b).naturality]
          simp only [Category.assoc, pushout.condition])
    have hPO' : IsPushout ((u a).app K ≫ pushout.inl _ _) (D.map L.hom) w'
        ((u a).app (Kp L) ≫ pushout.inl _ _) :=
      isPushout_pushouts (po_stage (fun k => (hpush a k).1) (φ L))
        (po_stage (fun k => (hpush b k).1) (φ L))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    have hw' : v''.app L ≫ ((hpush'' L).1.isoIsPushout _ _ hPO').hom = w' :=
      IsPushout.inl_isoIsPushout_hom _ _ (hpush'' L).1 hPO'
    have hwt : ((onRings F).map w').hom t = 0 := by
      rw [← hw', map_comp_apply, hvL, map_zero]
    simp only [t, map_sub, sub_eq_zero, ← map_comp_apply, w', pushout.inl_desc,
      pushout.inr_desc] at hwt
    simpa only [s', ← map_comp_apply] using hwt
  choose L0 hL0 using hover
  obtain ⟨Lc, hLc⟩ := IsFiltered.sup_objs_exists (Finset.univ.image (fun p : ι × ι => L0 p.1 p.2))
  have ψ : ∀ a b, L0 a b ⟶ Lc := fun a b =>
    (hLc (Finset.mem_image_of_mem (fun p : ι × ι => L0 p.1 p.2) (Finset.mem_univ (a, b)))).some
  let e' : ∀ i, D.obj Lc.right ⟶ (D' i).obj (Kp Lc) := fun i => (u i).app (Kp Lc)
  obtain ⟨y, hy⟩ := glue F e'
    (fun i => etale_inr (hpush i (Kp Lc)).1 (hsq i).1)
    (cover_inr g' (D.map (Kp Lc).hom) (fun i => (v i).app (Kp Lc)) e'
      (fun i => (hpush i _).1) hcov')
    (s' Lc) (fun a b => hL0 a b Lc (ψ a b))
  refine ⟨Lc.right, y, ?_⟩
  apply sep F g hg hcov
  intro i
  have hu : e' i ≫ (ιB i).app (Kp Lc) = c.ι.app Lc.right ≫ g i := (hpush i _).2.2
  rw [← map_comp_apply, ← hu, map_comp_apply, hy i]
  simp only [s']
  rw [← map_comp_apply, cocone_nat, hs]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

theorem finitary_of_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → Finitary F := by
  intro R _ M F η hM hloc hker
  have hinj := GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit R M F η hM hloc hker
  show PreservesFilteredColimitsOfSize.{0, 0} (onRings F)
  refine (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ (onRings F)).2.2 ?_
  intro J _ _ D c hc
  exact ⟨surj M F η hM hloc hinj J D c hc, hinj J D c hc⟩

end GlobalTheory.EtC.FinitaryOfLocBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPowSmulEqZeroOfResBasicOpen
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem form_pow_smul_eq_zero_of_res_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩

theorem form_eq_zero_of_basis_cover : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (ω : Ω[(OAff s').obj T⁄R']), (∀ t (u : T ⟶ G.obj t), p1 (OAff s') u ω = 0) → ω = 0) := by
  intro R' _ X' s' C' _ G hcov T ω hω
  obtain ⟨n, b, hspan, hb⟩ := hcov T
  let A := (OAff s').obj T
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  have hpow : ∀ i, ∃ m : ℕ, b i ^ m ∈ J := by
    intro i
    have hU : IsAffineOpen (X'.basicOpen (show Γ(X', T.unop.1) from b i)) :=
      T.unop.2.basicOpen _
    have hle : (⟨X'.basicOpen (show Γ(X', T.unop.1) from b i), hU⟩ : X'.affineOpens) ≤ T.unop :=
      X'.basicOpen_le _
    have hunit : IsUnit (mp (OAff s') (homOfLE hle).op (b i)) :=
      X'.toRingedSpace.isUnit_res_basicOpen (show Γ(X', T.unop.1) from b i)
    obtain ⟨t, v, w, hvw⟩ := hb i _ (homOfLE hle).op hunit
    have h0 : p1 (OAff s') (homOfLE hle).op ω = 0 := by
      rw [← hvw, oneFormsMapOfFunctorMorphism_comp, hω t v, map_zero]
    obtain ⟨m, hm⟩ := form_pow_smul_eq_zero_of_res_basicOpen s' T.unop _ hU hle ω h0
    exact ⟨m, (Submodule.mem_annihilator_span_singleton ω _).2 hm⟩
  choose m hm using hpow
  have hJ : J = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan (∑ i, m i), Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change b i ^ (∑ j, m j) ∈ J
    rw [← Nat.add_sub_cancel' hmi, pow_add]
    exact J.mul_mem_right _ (hm i)
  have h1 : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZero
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem functionFieldPlaceOrder_inv {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (hx : x ≠ 0) :
    ord v x⁻¹ = - ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ord
  rw [map_inv₀, WithZero.log_inv, neg_neg]

theorem adjoin_simple_inv_eq (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

theorem finite_support_and_sum_ord_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  intro k F _ _ _ _ _ hF x hx
  by_cases htr : Transcendental k x
  · have htr' : Transcendental k x⁻¹ := by
      intro h
      apply htr
      have := h.inv
      rwa [inv_inv] at this
    obtain ⟨hA, hsA⟩ := _root_.GlobalTheory.Nef.zeros_finite_sum_eq_degree k F hF x htr
    obtain ⟨hB, hsB⟩ := _root_.GlobalTheory.Nef.zeros_finite_sum_eq_degree k F hF x⁻¹ htr'
    rw [adjoin_simple_inv_eq] at hsB
    set A := {v : Place k F | v.1 x < 1}
    set B := {v : Place k F | v.1 x⁻¹ < 1}
    have hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B := by
      intro v hv
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hv with h | h
      · exact Or.inl h
      · right
        show v.1 x⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
    refine ⟨(hA.union hB).subset hsub, ?_⟩
    have hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v := by
      intro v
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_trichotomy (v.1 x) 1 with h | h | h
      · have hB' : v ∉ B := by
          show ¬ v.1 x⁻¹ < 1
          rw [map_inv₀, not_lt]
          exact (one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le
        rw [Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]
      · have e : ord v x = 0 := by unfold ord; rw [h, WithZero.log_one, neg_zero]
        rw [e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'),
          Set.indicator_of_notMem (show v ∉ B from by
            show ¬ v.1 x⁻¹ < 1
            rw [map_inv₀, h, inv_one]; exact lt_irrefl _)]
        simp
      · have hA' : v ∉ A := fun h' => lt_asymm h h'
        have hB' : v ∈ B := by
          show v.1 x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h
        rw [Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]
    have hfA : (Function.support (A.indicator fun w => ord w x)).Finite :=
      hA.subset (Set.support_indicator_subset)
    have hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite :=
      hB.subset (Set.support_indicator_subset)
    rw [finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]
  · have halg : IsAlgebraic k x := by
      by_contra h
      exact htr h
    have hint : IsIntegral k x := halg.isIntegral
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k x hdeg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1 := fun v => v.2.2 c hc
    refine ⟨by simp [hv], ?_⟩
    have : ∀ v : Place k F, ord v (algebraMap k F c) = 0 := by
      intro v; unfold ord; rw [hv v, WithZero.log_one, neg_zero]
    simp [this]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexScaledUniformiser
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem local_index_scaled : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF v n M d hM hMinv
  obtain ⟨hmul, hzpow, -, -, -, ⟨π, hπ0, hπ⟩, -⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v

  have hvπ : v.1 π = WithZero.exp (-1) := by
    have hne : v.1 π ≠ 0 := by simpa using hπ0
    have : WithZero.log (v.1 π) = -1 := by
      unfold ord at hπ; omega
    rw [← this, WithZero.exp_log hne]
  set c : F := π ^ d with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero _ hπ0
  have hvc : v.1 c = WithZero.exp (-(d : ℤ)) := by
    rw [hcdef, map_pow, hvπ]
    show WithZero.exp (-1) ^ d = _
    rw [← WithZero.exp_nsmul]; congr 1; simp
  set h : Matrix (Fin n) (Fin n) F := c⁻¹ • M with hhdef
  have hdet : h.det = (c⁻¹) ^ n * M.det := by rw [hhdef, Matrix.det_smul, Fintype.card_fin]
  have hdet0 : h.det ≠ 0 := by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hM
  have hinv : h⁻¹ = c • M⁻¹ := by
    rw [hhdef]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
  have hinvb : ∀ i j, v.1 (h⁻¹ i j) ≤ 1 := by
    intro i j
    rw [hinv, Matrix.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (M⁻¹ i j) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hMinv i j
      _ = 1 := by rw [← WithZero.exp_add]; simp
  obtain ⟨N, φ₀, hN, hφ₀⟩ := _root_.GlobalTheory.Nef.local_index k F hFF v n h hdet0 hinvb

  have hord : ord v h.det = -(n * d : ℤ) + ord v M.det := by
    have e : (c⁻¹) ^ n = π ^ (-(n * d : ℤ)) := by
      rw [hcdef, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
    rw [hdet, hmul _ _ (pow_ne_zero _ (inv_ne_zero hc0)) hM, e, hzpow π hπ0, hπ, mul_one]
  let sc : (Fin n → F) →ₗ[k] (Fin n → F) :=
    { toFun := fun p => c • p
      map_add' := fun p q => smul_add c p q
      map_smul' := fun a p => by
        ext i
        show c * (a • p i) = a • (c * p i)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N, φ₀ ∘ₗ sc, by rw [hN, hord]; ring, ?_⟩
  intro p hp hφ i
  have hx : ∀ i, v.1 ((c • p) i) ≤ 1 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (p i) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hp i
      _ = 1 := by rw [← WithZero.exp_add]; simp
  have := hφ₀ (c • p) hx hφ i
  have e2 : h.mulVec (c • p) = M.mulVec p := by
    rw [hhdef, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rwa [e2] at this

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUniversStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i := by
  first | (exact @GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (exact GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (intros; apply GlobalTheory.EtC.GalSec.Tens.lcRing_universal  <;> assumption)
end

