module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0028
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0032
public import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0008
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0029
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0033
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0063
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyAndLiftOfLocallySurjectiveExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem restriction_trans {F : Shv ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

private theorem res_map_of_sheaf_morphism {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U) (b : Sec F U) :
    Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem map_map_eq_zero {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) (h : φ ≫ ψ = 0) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = 0 := by
  have h2 := congrArg (fun t : F ⟶ H => (t.hom.app (op U)).hom a) h
  simpa [Sec.map] using h2

private theorem local_bind {U : Scheme.{0}} {P R : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => R W (k ≫ g)) : Loc U R := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose T hT hTR using fun (V : Scheme.{0}) (g : V ⟶ U) (H : S.arrows g) => h V g (hSP V g H)
  refine ⟨Sieve.bind S.arrows fun Y f H => T Y f H, ?_, ?_⟩
  · exact Scheme.etaleTopology.bind_covering hS fun Y f H => hT Y f H
  · rintro W _ ⟨Y, k, g, H, hk, rfl⟩
    exact hTR Y g H W k hk

theorem UpperTheory.acy_and_lift_of_locally_surjective_exact :
    ∀ (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → ∀ (A C₁ Z : Shv ℤ) (i : A ⟶ C₁) (d : C₁ ⟶ Z) (w : i ≫ d = 0), Mono i → (ShortComplex.mk i d w).Exact → (∀ U : Scheme.{0}, Q U → ∀ b : Sec Z U, Loc U fun V g => ∃ a : Sec C₁ V, Sec.map d a = Sec.res g b) → Acy Q A → Acy Q C₁ → Acy Q Z ∧ ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ Z, ∃ h : (free ℤ).obj P ⟶ C₁, h ≫ d = f := by
  intro Q hQ A C₁ Z i d w hi hex hloc hA hC
  have hfac : Abelian.factorThruImage d ≫ Abelian.image.ι d = d := Abelian.image.fac d
  have w1 : i ≫ Abelian.factorThruImage d = 0 := by
    rw [← cancel_mono (Abelian.image.ι d), Category.assoc, hfac, w, zero_comp]
  let S1 := ShortComplex.mk i (Abelian.factorThruImage d) w1
  have hS1ex : S1.Exact := by
    let φ : S1 ⟶ ShortComplex.mk i d w :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι d
        comm₁₂ := by simp [S1]
        comm₂₃ := by simp [S1, hfac] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  have hS1 : S1.ShortExact := { exact := hS1ex, mono_f := hi, epi_g := by dsimp [S1]; infer_instance }
  have w2 : Abelian.image.ι d ≫ cokernel.π d = 0 := by
    rw [← cancel_epi (Abelian.factorThruImage d), ← Category.assoc, hfac, cokernel.condition, comp_zero]
  let S2 := ShortComplex.mk (Abelian.image.ι d) (cokernel.π d) w2
  have hS2 : S2.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := by dsimp [S2]; infer_instance
      epi_g := by dsimp [S2]; infer_instance }
  have hsub : ∀ U : Scheme.{0}, Q U → Subsingleton (Sec (cokernel d) U) := by
    intro U hU
    refine ⟨fun s t => ?_⟩
    have hz : ∀ s : Sec (cokernel d) U, s = 0 := by
      intro s
      have hl := ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (cokernel.π d)).2.2.1.1 inferInstance) U s
      have hl2 : Loc U fun W k => Sec.res k s = Sec.res k (0 : Sec (cokernel d) U) := by
        refine local_bind hl ?_
        rintro V g ⟨z, hz⟩
        obtain ⟨T, hT, hTz⟩ := hloc V (hQ g hU) z
        refine ⟨T, hT, ?_⟩
        rintro W k hk
        obtain ⟨a, ha⟩ := hTz W k hk
        rw [restriction_trans, ← hz, res_map_of_sheaf_morphism, ← ha, map_map_eq_zero d (cokernel.π d) (cokernel.condition d)]
        simp [Sec.res]
      exact (_root_.GlobalTheory.EtC.sec_ext_glue ℤ (cokernel d) U).1 s 0 hl2
    rw [hz s, hz t]
  have hI : Acy Q (Abelian.image d) := UpperTheory.acy_right_of_shortExact Q S1 hS1 hA hC
  have hK : Acy Q (cokernel d) := fun P hP n _ => UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q _ hsub P hP n
  refine ⟨UpperTheory.acy_middle_of_shortExact Q S2 hS2 hI hK, ?_⟩
  intro P hP f
  obtain ⟨h1, hh1⟩ := UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections Q S2 hS2 hsub P hP f
  obtain ⟨h2, hh2⟩ := UpperTheory.exists_lift_free_to_middle_of_shortExact_acy Q S1 hS1 hA P hP h1
  refine ⟨h2, ?_⟩
  dsimp [S1, S2] at hh1 hh2
  rw [← hfac, ← Category.assoc, hh2, hh1]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClosedFiberColimitPresentation
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf LateralTheory.E.LeafVanBStalkPf

namespace UpperTheory.PushoutColimitSpec

private theorem epi_of_closed {R S : CommRingCat.{0}} (q : R ⟶ S) [IsClosedImmersion (Spec.map q)] : Epi q :=
  ⟨fun a b h => Spec.map_injective ((cancel_mono (Spec.map q)).1 (by
    rw [← Spec.map_comp, ← Spec.map_comp, h]))⟩

private theorem isPushout_of_Spec {A B C P : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (inl : B ⟶ P) (inr : C ⟶ P)
    (h : IsPullback (Spec.map inl) (Spec.map inr) (Spec.map f) (Spec.map g)) : IsPushout f g inl inr := by
  have hw : f ≫ inl = g ≫ inr := Spec.map_injective (by simpa using h.w)
  have h' : IsPullback inl.op inr.op f.op g.op :=
    IsPullback.of_map Scheme.Spec (by rw [← op_comp, ← op_comp, hw]) h
  exact h'.unop.flip

private def colimOfPushout {J : Type} [SmallCategory J] {D D' : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c)
    (c' : Cocone D') (q : ∀ j, D.obj j ⟶ D'.obj j)
    (hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g) (hepi : ∀ j, Epi (q j))
    (qi : c.pt ⟶ c'.pt) (hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j) (j0 : J)
    (hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0)) : IsColimit c' :=
  let f (s : Cocone D') : c.pt ⟶ s.pt := hc.desc
    ⟨s.pt, { app := fun j => q j ≫ s.ι.app j
             naturality := fun j j' g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               rw [← Category.assoc, hq, Category.assoc, s.w] }⟩
  have hf (s : Cocone D') (j : J) : c.ι.app j ≫ f s = q j ≫ s.ι.app j := hc.fac _ j
  { desc := fun s => hp.desc (f s) (s.ι.app j0) (hf s j0)
    fac := fun s j => by
      have := hepi j
      rw [← cancel_epi (q j), ← Category.assoc, ← hqi, Category.assoc, hp.inl_desc, hf]
    uniq := fun s m hm => by
      apply hp.hom_ext
      · rw [hp.inl_desc]
        apply hc.hom_ext
        intro j
        rw [← Category.assoc, hqi, Category.assoc, hm, hf]
      · rw [hp.inr_desc, hm] }

private theorem ring_system {J : Type} [SmallCategory J] (Z : J → Scheme.{0}) [∀ j, IsAffine (Z j)]
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (hid : ∀ j, r (𝟙 j) = 𝟙 _)
    (hcomp : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), r (g ≫ g') = r g' ≫ r g) :
    ∃ (D' : J ⥤ CommRingCat.{0}) (ez : ∀ j, Z j ≅ Spec (D'.obj j)),
      ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g) := by
  refine ⟨{ obj := fun j => Γ(Z j, ⊤)
            map := fun {j j'} g => Spec.preimage ((Z j').isoSpec.inv ≫ r g ≫ (Z j).isoSpec.hom)
            map_id := fun j => Spec.map_injective (by simp [hid])
            map_comp := fun {j j' j''} g g' => Spec.map_injective (by simp [hcomp]) },
    fun j => (Z j).isoSpec, fun {j j'} g => ?_⟩
  simp

private theorem cocone_system {J : Type} [SmallCategory J] [Nonempty J] (Z : J → Scheme.{0})
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (D D' : J ⥤ CommRingCat.{0})
    (ez : ∀ j, Z j ≅ Spec (D'.obj j))
    (hr : ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g))
    (c : Cocone D) (hc : IsColimit c) (φ : ∀ j, Z j ⟶ Spec (D.obj j)) [∀ j, IsClosedImmersion (φ j)]
    (hφ : ∀ {j j' : J} (g : j ⟶ j'), r g ≫ φ j = φ j' ≫ Spec.map (D.map g))
    (Zi : Scheme.{0}) [IsAffine Zi] (φi : Zi ⟶ Spec c.pt) (l : ∀ j, Zi ⟶ Z j)
    (hl : ∀ {j j' : J} (g : j ⟶ j'), l j' ≫ r g = l j)
    (hlφ : ∀ j, l j ≫ φ j = φi ≫ Spec.map (c.ι.app j))
    (hpb : ∀ j, IsPullback (l j) φi (φ j) (Spec.map (c.ι.app j))) :
    ∃ (c' : Cocone D') (_ : IsColimit c') (ei : Zi ≅ Spec c'.pt),
      ∀ j, ei.inv ≫ l j ≫ (ez j).hom = Spec.map (c'.ι.app j) := by
  let q : ∀ j, D.obj j ⟶ D'.obj j := fun j => Spec.preimage ((ez j).inv ≫ φ j)
  have hqs : ∀ j, Spec.map (q j) = (ez j).inv ≫ φ j := fun j => Spec.map_preimage _
  let c' : Cocone D' :=
    { pt := Γ(Zi, ⊤)
      ι := { app := fun j => Spec.preimage (Zi.isoSpec.inv ≫ l j ≫ (ez j).hom)
             naturality := fun j j' g => Spec.map_injective (by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Spec.map_comp,
                 Spec.map_preimage, ← hr g, Category.assoc, Iso.hom_inv_id_assoc]
               rw [← Category.assoc (l j'), hl g, ← Category.assoc]) } }
  have hcs : ∀ j, Spec.map (c'.ι.app j) = Zi.isoSpec.inv ≫ l j ≫ (ez j).hom := fun j => Spec.map_preimage _
  let qi : c.pt ⟶ c'.pt := Spec.preimage (Zi.isoSpec.inv ≫ φi)
  have hqis : Spec.map qi = Zi.isoSpec.inv ≫ φi := Spec.map_preimage _
  have hepi : ∀ j, Epi (q j) := fun j => by
    have : IsClosedImmersion (Spec.map (q j)) := by rw [hqs]; infer_instance
    exact epi_of_closed _
  have hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g := fun {j j'} g =>
    Spec.map_injective (by
      simp only [Spec.map_comp, hqs, ← hr g, Category.assoc, Iso.hom_inv_id_assoc, hφ g])
  have hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j := fun j => Spec.map_injective (by
    simp only [Spec.map_comp, hqs, hcs, hqis, Category.assoc, Iso.hom_inv_id_assoc, hlφ])
  obtain ⟨j0⟩ := ‹Nonempty J›
  have hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0) := by
    apply isPushout_of_Spec
    refine IsPullback.of_iso (hpb j0).flip Zi.isoSpec (Iso.refl _) (ez j0) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hqis]
    · simp [hcs]
    · simp
    · simp [hqs]
  exact ⟨c', colimOfPushout hc c' q hq hepi qi hqi j0 hp, Zi.isoSpec, fun j => (hcs j).symm⟩

end UpperTheory.PushoutColimitSpec

open UpperTheory.PushoutColimitSpec in
theorem UpperTheory.exists_closedFiber_colimit_presentation :
    ∀ {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (x : U.left) (S : SHSys U x)
        (zl : ∀ j, pullback (S.t ≫ U.hom) ι ⟶ pullback (S.V j).hom ι),
        (∀ j, zl j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) ≫ (S.e j).inv) →
        (∀ j, zl j ≫ pullback.snd _ _ = pullback.snd _ _) →
        ∃ (D' : S.J ⥤ CommRingCat.{0}) (c' : Cocone D') (_ : IsColimit c')
          (ez : ∀ j, pullback (S.V j).hom ι ≅ Spec (D'.obj j)) (ei : pullback (S.t ≫ U.hom) ι ≅ Spec c'.pt),
          (∀ {j j' : S.J} (g : j ⟶ j'), (ez j').inv ≫ resBW ι (S.tr g) ≫ (ez j).hom = Spec.map (D'.map g)) ∧
          (∀ j, ei.inv ≫ zl j ≫ (ez j).hom = Spec.map (c'.ι.app j)) := by
  intro B W ι _ U x S zl h1 h2
  have rfst : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (S.tr g).left := fun g => pullback.lift_fst _ _ _
  have rsnd : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.snd _ _ = pullback.snd _ _ := fun g =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have htr : ∀ {j j' : S.J} (g : j ⟶ j'),
      (S.tr g).left = (S.e j').hom ≫ Spec.map (S.D.map g) ≫ (S.e j).inv := fun g => by
    rw [← S.tr_spec g]; simp
  have hid : ∀ j, resBW ι (S.tr (𝟙 j)) = 𝟙 _ := fun j => by
    apply pullback.hom_ext
    · rw [rfst, htr]; simp
    · rw [rsnd]; simp
  have hcomp : ∀ {j j' j'' : S.J} (g : j ⟶ j') (g' : j' ⟶ j''),
      resBW ι (S.tr (g ≫ g')) = resBW ι (S.tr g') ≫ resBW ι (S.tr g) := fun g g' => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, rfst, reassoc_of% (rfst g'), htr, htr, htr]; simp
    · rw [Category.assoc, rsnd, rsnd, rsnd]
  have hVa : ∀ j, IsAffine (S.V j).left := fun j => .of_isIso (S.e j).hom
  let φ : ∀ j, pullback (S.V j).hom ι ⟶ Spec (S.D.obj j) := fun j => pullback.fst _ _ ≫ (S.e j).hom
  have hφc : ∀ j, IsClosedImmersion (φ j) := fun j => inferInstance
  have hZa : ∀ j, IsAffine (pullback (S.V j).hom ι) := fun j => by
    have h := (IsClosedImmersion.isAffine_surjective_of_isAffine (φ j)).1
    exact h
  have hZi : IsAffine (pullback (S.t ≫ U.hom) ι) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst (S.t ≫ U.hom) ι)).1
  obtain ⟨D', ez, hr⟩ := ring_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) hid hcomp
  have hφ : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ φ j = φ j' ≫ Spec.map (S.D.map g) := fun {j j'} g => by
    simp only [φ]
    rw [reassoc_of% (rfst g), htr]; simp
  have hl : ∀ {j j' : S.J} (g : j ⟶ j'), zl j' ≫ resBW ι (S.tr g) = zl j := fun {j j'} g => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, reassoc_of% (h1 j'), h1, htr]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp_assoc, S.c.w]
    · rw [Category.assoc, rsnd, h2, h2]
  have hlφ : ∀ j, zl j ≫ φ j = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) := fun j => by
    simp only [φ]
    rw [reassoc_of% (h1 j)]; simp
  have hpb : ∀ j, IsPullback (zl j) (pullback.fst (S.t ≫ U.hom) ι) (φ j) (Spec.map (S.c.ι.app j)) := fun j => by
    have hw : (S.a j).left ≫ U.hom = (S.V j).hom := by simpa using (S.a j).w
    have hb : (Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom = S.t ≫ U.hom := by
      rw [S.ht j, ← hw]; simp
    have big : IsPullback (zl j ≫ pullback.snd _ _) (pullback.fst (S.t ≫ U.hom) ι) ι
        ((Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom) := by
      rw [h2, hb]; exact (IsPullback.of_hasPullback _ _).flip
    have sq := IsPullback.of_right big (h1 j) (IsPullback.of_hasPullback (S.V j).hom ι).flip
    exact IsPullback.of_iso sq (Iso.refl _) (Iso.refl _) (Iso.refl _) (S.e j) (by simp) (by simp) (by simp [φ]) (by simp)
  have : Nonempty S.J := IsFiltered.nonempty
  obtain ⟨c', hc', ei, he⟩ := cocone_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) S.D D' ez hr
    S.c S.hc φ hφ (pullback (S.t ≫ U.hom) ι) (pullback.fst _ _) zl hl hlφ hpb
  exact ⟨D', c', hc', ez, ei, hr, he⟩
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsInjectiveH1GmToPic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace UpperTheory.PicD

private def SF (F : Shv ℤ) : CommRingCat.{0} ⥤ AddCommGrpCat.{1} :=
  Scheme.Spec.rightOp ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} ℤ)) AddCommGrpCat.{1}

private def SFd {F G : Shv ℤ} (φ : F ⟶ G) : SF F ⟶ SF G :=
  Functor.whiskerLeft _ (Functor.whiskerRight φ.hom _)

private theorem res_res (F : Shv ℤ) {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T) (x : Sec F (Spec R)) :
    (Sec.res (Spec.map g) (Sec.res (Spec.map f) x) : Sec F (Spec T)) = Sec.res (Spec.map (f ≫ g)) x := by
  show (F.obj.map (Spec.map g).op).hom ((F.obj.map (Spec.map f).op).hom x) =
    (F.obj.map (Spec.map (f ≫ g)).op).hom x
  rw [Spec.map_comp, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private def uS (R : CommRingCat.{0}) (u : Rˣ) : Sec Gm (Spec R) :=
  unitSec (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom u)

private theorem uS_mul (R : CommRingCat.{0}) (u v : Rˣ) : uS R (u * v) = uS R u + uS R v := by
  unfold uS
  rw [map_mul, unitSec_mul]

private theorem uS_res {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Rˣ) :
    Sec.res (Spec.map f) (uS R u) = uS S (Units.map f.hom.toMonoidHom u) := by
  unfold uS
  rw [unitSec_res]
  congr 1
  ext
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom (u : R) =
    (f ≫ (Scheme.ΓSpecIso S).inv).hom (u : R)
  rw [Scheme.ΓSpecIso_inv_naturality]

private theorem uS_bij (R : CommRingCat.{0}) : Function.Bijective (uS R) := by
  have h2 : Function.Bijective (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom) := by
    let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
    exact (Units.mapEquiv e.toMulEquiv).bijective
  have h1 : Function.Bijective (unitSec (U := Spec R)) := UpperTheory.unitSections_multiplicativeGroup_bijective_affine R
  exact h1.comp h2

private def PD : Data where
  S0 := SF ((res ℤ Gm).X 0)
  S1 := SF ((res ℤ Gm).X 1)
  d := SFd ((res ℤ Gm).d 0 1)
  ι R := AddMonoidHom.mk' (fun u => (Sec.map (resι ℤ Gm) (uS R u.toMul) : Sec ((res ℤ Gm).X 0) (Spec R)))
    (fun u v => by
      show (Sec.map (resι ℤ Gm) (uS R (u.toMul * v.toMul)) : Sec ((res ℤ Gm).X 0) (Spec R)) = _
      rw [uS_mul]
      exact map_add _ _ _)
  ι_nat {R R'} f u := by
    have h := congrArg (fun φ => φ.hom (uS R u)) ((resι ℤ Gm).hom.naturality (Spec.map f).op)
    refine Eq.trans h.symm ?_
    show (Sec.map (resι ℤ Gm) (Sec.res (Spec.map f) (uS R u)) : Sec ((res ℤ Gm).X 0) (Spec R')) = _
    rw [uS_res]
    rfl
  ι_inj R u v h := by
    have h1 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).2.1 h
    exact Additive.toMul.injective ((uS_bij R).1 h1)
  d_eq_zero R w := by
    have h := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).1 w
    constructor
    · intro h0
      obtain ⟨a, ha⟩ := h.1 h0
      obtain ⟨u, rfl⟩ := (uS_bij R).2 a
      exact ⟨Additive.ofMul u, ha⟩
    · rintro ⟨u, hu⟩
      exact h.2 ⟨_, hu⟩
  glue A C _ _ _ _ _ w hw := (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 0) A C w hw).exists
  sep A C _ _ _ _ _ y y' hy := by
    refine (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 1) A C _ ?_).unique (y₁ := y) (y₂ := y') rfl hy.symm
    have hc : CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i1 A C).toRingHom =
        CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i2 A C).toRingHom := by
      ext a
      exact ((i1 A C).commutes a).trans ((i2 A C).commutes a).symm
    have hk : ∀ (y0 : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        (Sec.res (Spec.map (CommRingCat.ofHom (i1 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) :
            Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of (TensorProduct A C C)))) =
        Sec.res (Spec.map (CommRingCat.ofHom (i2 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) := fun y0 => by
      rw [res_res, res_res, hc]
    exact hk y

end UpperTheory.PicD

set_option maxHeartbeats 1000000 in
open UpperTheory.PicD in
theorem UpperTheory.exists_injective_h1_gm_to_pic :
    ∀ (A : Type) [CommRing A], ∃ φ : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A), Function.Injective φ := by
  intro A _
  let X := Spec (CommRingCat.of A)
  let Z : AddSubgroup (PD.S1.obj (CommRingCat.of A)) :=
    ((SFd ((res ℤ Gm).d 1 2)).app (CommRingCat.of A)).hom.ker
  have hZ : ∀ z ∈ Z, PD.LocEx z := fun z hz => UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary A z hz
  obtain ⟨ψ, hψ⟩ := PD.main A Z hZ
  have hT := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff ℤ X (res ℤ Gm) 0 1 2 (by norm_num) (by norm_num)
  let e : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 → Sec ((res ℤ Gm).X 1) X :=
    fun α => ev (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1) 0 1 (by norm_num) X (𝟙 X)
  have hmem : ∀ α, e α ∈ Z := fun α => AddMonoidHom.mem_ker.mpr (hT.2 α).1
  let τ : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 →+ Z :=
    { toFun := fun α => ⟨e α, hmem α⟩
      map_zero' := by
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (0 : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          0 0 1 (by norm_num) X (𝟙 X)).2.2.1
      map_add' := by
        intro α β
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          β 0 1 (by norm_num) X (𝟙 X)).1 }
  have hf : coboundaries ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 ≤ (ψ.comp τ).ker := by
    intro α hα
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hψ]
    exact ((hT.2 α).2.mp ((CohomologyClass.mk_eq_zero_iff α).mpr hα))
  refine ⟨CohomologyClass.descAddMonoidHom (ψ.comp τ) hf, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective c
  rw [CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.comp_apply, hψ] at hc
  exact (hT.2 α).2.mpr hc
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureFiniteOfFiniteTypeDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem UpperTheory.integralClosure_finite_of_finiteType_domain :
    LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := by
  intro Ω L _ _ _ u _ hfd
  have : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    .adjoin_of_finite (Set.finite_singleton u)
  refine GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial
    Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_
  intro s L' _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpr | rfl
  · haveI : Fact p.Prime := ⟨hpr⟩
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'
  · haveI : CharZero Ω := CharP.charP_to_charZero Ω
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ModuleFiniteIntegralClosureOfFiniteTypePerfect
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private theorem UpperTheory.integralClosure_finite_of_finiteType_perfect (k : Type) [Field k] [PerfectField k] (B L : Type)
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field L] [Algebra B L]
    [FaithfulSMul B L] [Algebra.EssFiniteType B L] :
    Module.Finite B (integralClosure B L) := by
  letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
  haveI : IsScalarTower B (FractionRing B) L := FractionRing.isScalarTower_liftAlgebra B L
  haveI : Algebra.EssFiniteType (FractionRing B) L :=
    Algebra.EssFiniteType.of_comp B (FractionRing B) L
  let M := algebraicClosure (FractionRing B) L
  haveI : FiniteDimensional (FractionRing B) M :=
    GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType (FractionRing B) L
  haveI : Module.Finite B (integralClosure B M) :=
    GlobalTheory.NormFin.finite_integralClosure_of_perfectField k B (FractionRing B) M
  let g : M →ₐ[B] L := M.val.restrictScalars B
  have hg : Function.Injective g := Subtype.val_injective
  let φ : integralClosure B M →ₗ[B] integralClosure B L :=
    { toFun := fun x => ⟨g x, x.2.map g⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro r x
        ext
        simp }
  refine Module.Finite.of_surjective φ ?_
  rintro ⟨y, hy⟩
  have hyF : IsIntegral (FractionRing B) y := hy.tower_top
  let z : M := ⟨y, mem_algebraicClosure_iff'.mpr hyF⟩
  have hz : IsIntegral B z := (isIntegral_algHom_iff g hg).mp hy
  exact ⟨⟨z, hz⟩, rfl⟩

theorem UpperTheory.module_finite_integralClosure_of_finiteType_perfect :
    ∀ (k : Type) [Field k] [PerfectField k] (A L : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field L] [Algebra A L] [Algebra.EssFiniteType A L], Module.Finite A (integralClosure A L) := by
  intro k _ _ A L _ _ _ _ _ _
  let I := RingHom.ker (algebraMap A L)
  letI : Algebra (A ⧸ I) L := (RingHom.kerLift (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (A ⧸ I) L :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ I) L).mpr (RingHom.kerLift_injective _)
  haveI : I.IsPrime := RingHom.ker_isPrime (algebraMap A L)
  haveI : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I
  haveI : Algebra.FiniteType k (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  haveI : Algebra.EssFiniteType (A ⧸ I) L := Algebra.EssFiniteType.of_comp A (A ⧸ I) L
  haveI : Module.Finite A (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ I) (integralClosure (A ⧸ I) L) :=
    UpperTheory.integralClosure_finite_of_finiteType_perfect k (A ⧸ I) L
  exact GlobalTheory.finite_integralClosure_of_finite_tower A (A ⧸ I) L
end

