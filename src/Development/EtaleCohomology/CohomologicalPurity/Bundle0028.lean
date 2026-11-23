module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0013
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0026
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0018
public import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0025
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0011
public import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvRPf
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0027

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
section
namespace LateralTheory.Fin.LeafExc
theorem etale_excision_identification_of_excision : LateralTheory.CohomologicalPurity.LeafExcIdent := by
  apply LateralTheory.CohomologicalPurity.EtaleExcIdent
theorem etale_excision_cohomological_degree_of_excision : LateralTheory.CohomologicalPurity.LeafExcDeg := by
  apply LateralTheory.CohomologicalPurity.LeafExcDeg_of
theorem etale_excision_formal_reduction_of_excision : LateralTheory.CohomologicalPurity.LeafExcFormal := by
  apply LateralTheory.CohomologicalPurity.LeafExcFormal_of <;> first | exact etale_excision_identification_of_excision | exact etale_excision_cohomological_degree_of_excision
theorem etale_excision_free_cokernel_injective_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCokInj := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCokInj_of
theorem etale_excision_cokernel_free_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCok := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCok_of_inj <;> first | exact etale_excision_free_cokernel_injective_of_excision
theorem etale_excision_surjective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafSurjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafSurjGeo_of
theorem etale_excision_injective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafInjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafInjGeo_of
theorem etale_excision_sheaf_level_of_excision : LateralTheory.CohomologicalPurity.LeafExcSheaf := by
  apply LateralTheory.CohomologicalPurity.LeafExcSheaf_of <;> first | exact etale_excision_cokernel_free_of_excision | exact etale_excision_surjective_geometric_points_of_excision | exact etale_excision_injective_geometric_points_of_excision
theorem etale_excision_isomorphism_of_excision : LateralTheory.CohomologicalPurity.LeafExc := by
  apply LateralTheory.CohomologicalPurity.LeafExc_of <;> first | exact etale_excision_formal_reduction_of_excision | exact etale_excision_sheaf_level_of_excision
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafExc := etale_excision_isomorphism_of_excision
end LateralTheory.Fin.LeafExc
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin
section
theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCokIsoPf
section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

def LeafFreePb : Prop := ∀ (R : Type) [CommRing R] {A' A B' B : PSh} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
  (b : A ⟶ B), IsPullback t l r b → Mono r → Mono b →
  IsPullback ((free R).map t) ((free R).map l) ((free R).map r) ((free R).map b)

theorem isIso_cokernel_map_of_pb_epi {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b)
    (he : Epi (biprod.desc r b)) : IsIso (cokernel.map _ _ _ _ sq.w) := by
  have := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map _ _ _ _ sq.w) := by
    have h1 : biprod.desc r b ≫ cokernel.π b = (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b) := by
      ext <;> simp
    have h3 : Epi (r ≫ cokernel.π b) := by
      have : Epi ((biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b)) := by rw [← h1]; infer_instance
      exact epi_of_epi (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) _
    have h2 : cokernel.π t ≫ cokernel.map _ _ _ _ sq.w = r ≫ cokernel.π b := by simp
    rw [← h2] at h3
    exact epi_of_epi (cokernel.π t) _
  exact isIso_of_mono_of_epi _

theorem transport_sq {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
    (ht : t = e₁.hom ≫ t' ≫ e₂.inv) (hl : l = e₁.hom ≫ l' ≫ e₃.inv)
    (hr : r = e₂.hom ≫ r' ≫ e₄.inv) (hb : b = e₃.hom ≫ b' ≫ e₄.inv)
    (sq : IsPullback t' l' r' b') (he : Epi (biprod.desc r' b')) :
    IsPullback t l r b ∧ Epi (biprod.desc r b) := by
  subst ht hl hr hb
  refine ⟨sq.of_iso e₁.symm e₂.symm e₃.symm e₄.symm (by simp) (by simp) (by simp) (by simp), ?_⟩
  have : biprod.desc (e₂.hom ≫ r' ≫ e₄.inv) (e₃.hom ≫ b' ≫ e₄.inv) =
      (biprod.mapIso e₂ e₃).hom ≫ biprod.desc r' b' ≫ e₄.inv := by
    ext <;> simp
  rw [this]
  infer_instance

theorem leafCokIso_of (hF : LeafFreePb) : LeafCokIso := by
  intro q P' P φ hpb hc n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    have key : ∀ {E' E : Spc} (f : E' ⟶ E), ((chains (ZMod q)).map f).f (-(p : ℤ)) =
        (HomologicalComplex.extendXIso _ _ h).hom ≫ (free (ZMod q)).map (f.app (op (SimplexCategory.mk p))) ≫
          (HomologicalComplex.extendXIso _ _ h).inv := by
      intro E' E f
      change (HomologicalComplex.extendMap ((chainsN (ZMod q)).map f) _).f _ = _
      rw [HomologicalComplex.extendMap_f _ _ h]
      rfl
    have hpb' : IsPullback (P'.hom.app (op (SimplexCategory.mk p))) (φ.left.app (op (SimplexCategory.mk p)))
        (φ.right.app (op (SimplexCategory.mk p))) (P.hom.app (op (SimplexCategory.mk p))) :=
      hpb.map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have mr : Mono (φ.right.app (op (SimplexCategory.mk p))) := by
      have := hc.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    have mb : Mono (P.hom.app (op (SimplexCategory.mk p))) := by
      have := hc.2.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    obtain ⟨h1, h2⟩ := transport_sq _ _ _ _ (key P'.hom) (key φ.left) (key φ.right) (key P.hom)
      (hF (ZMod q) _ _ _ _ hpb' mr mb) (hc.2.2 _)
    exact isIso_cokernel_map_of_pb_epi h1 h2
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains (ZMod q)).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hA : IsZero (cokernel ((chains (ZMod q)).map P'.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    have hB : IsZero (cokernel ((chains (ZMod q)).map P.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    exact ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem off_map_le {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (J : Ideal A) :
    off B (J.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A J := by
  intro x hx
  change x ∈ (PrimeSpectrum.zeroLocus _)ᶜ at hx
  change PrimeSpectrum.comap φ x ∈ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  intro h; apply hx
  rw [PrimeSpectrum.mem_zeroLocus] at h
  exact (Ideal.map_le_iff_le_comap.2 h : J.map φ ≤ _)

theorem opnMap_comp' {X'' X' X : Scheme.{0}} (k : X'' ⟶ X) (g : X'' ⟶ X') (f : X' ⟶ X) (hk : k = g ≫ f)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h1 : U'' ≤ g ⁻¹ᵁ U') (h2 : U' ≤ f ⁻¹ᵁ U)
    (h : U'' ≤ k ⁻¹ᵁ U) : opnMap k U'' U h = opnMap g U'' U' h1 ≫ opnMap f U' U h2 := by
  subst hk
  apply Arrow.hom_ext
  · change sch.map (Scheme.Hom.resLE (g ≫ f) U U'' h) =
      sch.map (Scheme.Hom.resLE g U' U'' h1) ≫ sch.map (Scheme.Hom.resLE f U U' h2)
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map (g ≫ f) = sch.map g ≫ sch.map f
    exact Functor.map_comp _ _ _

theorem leafExcAff_pf : LeafExcAff := by
  intro hyp hIE d q _ R B C _ _ _ ψ η hq hψ I K hη hK hI
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI; subst hK
  have hJfg : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hIfg := hJfg.map ψ
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by
    simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqB : IsUnit (q : B) := by simpa using hqP.map ψ
  have e1 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q ψ _ hJfg (indNbhd_of_nbhd ψ _ hψ) hqP (off_map_le ψ _)
  have e2 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q η _ hIfg hη hqB (off_map_le η _)
  have hle : off C ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ |>.map η) ≤
      Spec.map (CommRingCat.ofHom (η.comp ψ)) ⁻¹ᵁ off _ (Ideal.span (Set.range MvPolynomial.X)) := by
    rw [Ideal.map_map]; exact off_map_le _ _
  refine ⟨hle, ?_⟩
  have hs : Spec.map (CommRingCat.ofHom (η.comp ψ)) =
      Spec.map (CommRingCat.ofHom η) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]; rfl
  rw [opnMap_comp' _ _ _ hs _ _ _ (off_map_le η _) (off_map_le ψ _)]
  exact exc_comp q e2 e1

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPfSq
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)

private theorem inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
  pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _

private theorem inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
  pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _

theorem etale_double_inl_sigma_inl_eq_inl : dbl.inl (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = dbl.inl (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inl_sig φ)).trans (Category.id_comp _))

theorem etale_double_inr_sigma_inl_eq_retraction_jj_inr : dbl.inr (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = (rr φ ≫ jj φ) ≫ dbl.inr (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inr_sig φ)).trans
    ((Category.assoc (rr φ) (jj φ) (dbl.inl (QQ φ))).trans ((congrArg (rr φ ≫ ·) (jj_inl φ)).trans
      (Category.assoc (rr φ) (jj φ) (dbl.inr (QQ φ))).symm)))

theorem fix_key (q : ℕ) :
    (chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) =
      cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) := by
  have h := (chains (ZMod q)).map_isPushout (IsPushout.of_hasPushout (QQ φ).hom (QQ φ).hom)
  apply h.hom_ext
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inl (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      (congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inl_sigma_inl_eq_inl φ)))
  · have c0 : (chains (ZMod q)).map (dbl.inr (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) = 0 :=
      cokernel.condition _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inr (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      ((congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inr_sigma_inl_eq_retraction_jj_inr φ)).trans
      ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) ((chains (ZMod q)).map_comp (rr φ ≫ jj φ) (dbl.inr (QQ φ)))).trans
      ((Category.assoc _ _ _).trans ((congrArg ((chains (ZMod q)).map (rr φ ≫ jj φ) ≫ ·) c0).trans
      (Limits.comp_zero.trans c0.symm))))))

theorem LeafFix_of : LeafFix := by
  intro q n i P' P φ z hz
  have hr := (LateralTheory.CohomologicalPurity.eEquiv q n i (QQ φ)).right_inv ⟨z, hz⟩
  have hz1 : HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (tw q i) n
      (HK.pull (ZMod q) (LateralTheory.CohomologicalPurity.secC q (QQ φ)) (tw q i) n z) = z := congrArg Subtype.val hr
  change HK.pull (ZMod q) ((chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ))) (tw q i) n z = z
  conv_lhs => rw [← hz1]
  rw [← LateralTheory.CohomologicalPurity.HK.pull_comp', fix_key, hz1]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChiSq : Prop := ∀ {P' P : Arrow Spc} (φ : P' ⟶ P),
  IsPushout (dbl.inr P') (chi φ).right (dbl.map (chi φ)) (dbl.inr (QQ φ))

def LeafCokPush : Prop := ∀ (q : ℕ) {A B C D : Cx (ZMod q)} (f : A ⟶ B) (g : A ⟶ C) (a : B ⟶ D) (b : C ⟶ D)
  (h : IsPushout f g a b), IsIso (cokernel.map f b g a h.w)

theorem LeafCokPush_of : LeafCokPush := by
  intro q A B C D f g a b h
  refine ⟨⟨cokernel.desc b (h.desc (cokernel.π f) 0 (by simp)) (by simp), ?_, ?_⟩⟩
  · refine coequalizer.hom_ext ?_
    simp
  · refine coequalizer.hom_ext ?_
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply h.hom_ext <;> simp

theorem LeafChiExc_of (hS : LeafChiSq) : LeafChiExc := by
  intro q P' P φ
  exact LateralTheory.CohomologicalPurity.LeafExcCx_of LateralTheory.CohomologicalPurity.EtaleExcIdent q (chi φ)
    (LeafCokPush_of q _ _ _ _ ((chains (ZMod q)).map_isPushout (hS φ)))

theorem LeafExcOfEqv_of_sq (hS : LeafChiSq) : LeafExcOfEqv := LeafExcOfEqv_of LeafFix_of (LeafChiExc_of hS)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPf
section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem hk_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cone_map_congr {R : Type} [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (h : f₁ ≫ b = a ≫ f₂) (h' : f₁ ≫ b' = a' ≫ f₂) (ha : a = a') (hb : b = b') :
    mappingCone.map f₁ f₂ a b h = mappingCone.map f₁ f₂ a' b' h' := by
  subst ha; subst hb; rfl

theorem dbl_sq (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map P.hom ≫ (chains R).map (dbl.inl P) = (chains R).map P.hom ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (pushout.condition (f := P.hom) (g := P.hom))

def dblCone (R : Type) [CommRing R] (P : Arrow Spc) :
    mappingCone ((chains R).map P.hom) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map P.hom) ((chains R).map (dbl.inl P)) (dbl_sq R P)

theorem dblMap_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map (dbl.inr P') ≫ (chains R).map (dbl.map φ) = (chains R).map φ.right ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

def dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone ((chains R).map (dbl.inr P')) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map φ.right) ((chains R).map (dbl.map φ)) (dblMap_sq R φ)

theorem dblCone_nat (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    coneMap R φ ≫ dblCone R P = dblCone R P' ≫ dblConeMap R φ := by
  unfold coneMap dblCone dblConeMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  apply cone_map_congr
  · rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ)
  · rw [← Functor.map_comp, ← Functor.map_comp, inl_map]

theorem inr_dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone.inr _ ≫ dblConeMap R φ = (chains R).map (dbl.map φ) ≫ mappingCone.inr _ := by
  simp [dblConeMap, mappingCone.map]

def LeafDblConeQI : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → QuasiIso (dblCone R P)

def LeafConeSplit : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (g : K ⟶ L) (r : L ⟶ K), g ≫ r = 𝟙 K →
  ∀ (F : Shv R) (n : ℤ), Function.Injective (HK.pull R (mappingCone.inr g) F n) ∧
    ∀ y : HK R L F n, HK.pull R g F n y = 0 ↔ ∃ x, HK.pull R (mappingCone.inr g) F n x = y

theorem inr_fold_chains (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map (dbl.inr P) ≫ (chains R).map (dbl.fold P) = 𝟙 _ := by
  rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]

def psi (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) :
    HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n).codRestrict _ fun x =>
    ((hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n).2 _).2 ⟨x, rfl⟩

theorem psi_bij (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) : Function.Bijective (psi q P n i hS) := by
  have h := hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n
  refine ⟨fun a b hab => h.1 (congrArg Subtype.val hab), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (h.2 y.1).1 y.2
  exact ⟨x, Subtype.ext hx⟩

theorem leafHsRel_of (hD : LeafDblConeQI) (hS : LeafConeSplit) : LeafHsRel := by
  intro h1 q i
  let θ : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
      (HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hrel (ZMod q) P.hom (tw q i) n) :=
    fun P n h => by
      haveI := hD (ZMod q) P h
      exact AddEquiv.ofBijective (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n) (h1 (ZMod q) _ (tw q i) n)
  refine ⟨fun P n h => (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm.trans (θ P n h), ?_⟩
  intro P' P φ h' h n x
  have key : (AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x) =
      HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n
        ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x) := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    set y := (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x with hy
    have hx : x = psi q P n i hS y := by
      rw [hy]; exact ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).apply_symm_apply x).symm
    rw [hx]
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
        (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n y) =
      HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n (HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n y)
    rw [← hk_pull_comp, ← hk_pull_comp, inr_dblConeMap]
  change HK.pull (ZMod q) (dblCone (ZMod q) P') (tw q i) n
      ((AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x)) =
    HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n
      ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x))
  rw [key, ← hk_pull_comp, ← hk_pull_comp, dblCone_nat]

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWCechPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev vtx (n : ℕ) (i : Fin (n + 1)) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
  SimplexCategory.const _ _ i

def LeafCechRec : Prop := ∀ (X : Spc) (P Z : PSh) (φ : P ⟶ Z) (r : X ⟶ disc.obj Z)
  (g : X.obj (op (SimplexCategory.mk 0)) ⟶ P), g ≫ φ = r.app (op (SimplexCategory.mk 0)) →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : (X.obj (op (SimplexCategory.mk n))).obj U),
    (∀ i, g.app U ((X.map (vtx n i).op).app U x) = g.app U ((X.map (vtx n i).op).app U x')) → x = x') →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → P.obj U) (z : Z.obj U), (∀ i, φ.app U (y i) = z) →
    ∃ x, ∀ i, g.app U ((X.map (vtx n i).op).app U x) = y i) →
  ∃ ψ : X ⟶ (Arrow.mk φ).cechNerve, IsIso ψ ∧ ψ ≫ (Arrow.mk φ).augmentedCechNerve.hom = r

def LeafWData : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (r : W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) R)))))
    (g : (W d R).obj (op (SimplexCategory.mk 0)) ⟶
      yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))))),
    wa d R ≫ r = 𝟙 _ ∧ g ≫ yoneda.map (fW d R) = r.app (op (SimplexCategory.mk 0)) ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : ((W d R).obj (op (SimplexCategory.mk n))).obj U),
      (∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = g.app U (((W d R).map (vtx n i).op).app U x')) →
        x = x') ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → (yoneda.obj (Spec (CommRingCat.of
        (LaurentPolynomial (MvPolynomial (Fin d) R))))).obj U) (z : (yoneda.obj (Spec (CommRingCat.of
        (MvPolynomial (Fin d) R)))).obj U), (∀ i, (yoneda.map (fW d R)).app U (y i) = z) →
      ∃ x, ∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = y i)

theorem LeafWCech_of (hC : LeafCechRec) (hD : LeafWData) : LeafWCech := by
  intro d R _
  obtain ⟨r, g, hr, hg, hi, hs⟩ := hD d R
  obtain ⟨ψ, hψ, he⟩ := hC (W d R) _ _ (yoneda.map (fW d R)) r g hg hi hs
  refine ⟨ψ, hψ, ?_⟩
  change wa d R ≫ ψ ≫ (Arrow.mk (yoneda.map (fW d R))).augmentedCechNerve.hom = 𝟙 _
  subst he
  exact hr

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWCovPfB
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def LeafPLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), LocCov f g →
  ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))

theorem LeafCovLoc_of (hP : LeafPLoc) : LeafCovLoc := by
  intro R _ U V E f g hf hg hL
  refine ⟨hf, hg, fun n => ?_⟩
  let S := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let a := (freeP R).map (f.app n)
  let b := (freeP R).map (g.app n)
  have h1 : Epi (S.map (biprod.desc a b)) := by
    have : Sheaf.IsLocallySurjective (S.map (biprod.desc a b)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 (hP R f g hL n)
    infer_instance
  change Epi (biprod.desc (S.map a) (S.map b))
  let P := (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)
  let k : S.obj P ⟶ S.obj ((freeP R).obj (U.obj n)) ⊞ S.obj ((freeP R).obj (V.obj n)) :=
    biprod.lift (S.map (biprod.fst : P ⟶ _)) (S.map (biprod.snd : P ⟶ _))
  have h2 : k ≫ biprod.desc (S.map a) (S.map b) = S.map (biprod.desc a b) := by
    simp only [k]
    rw [biprod.lift_desc, ← S.map_comp, ← S.map_comp, ← S.map_add (f := _), biprod.desc_eq]
  rw [← h2] at h1
  exact epi_of_epi k _

theorem LeafWCov_of' (hG : LeafGeo) (hP : LeafPLoc) (hW : LeafWLoc) : LeafWCov :=
  LeafWCov_of hG (LeafCovLoc_of hP) hW

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWGmPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem intPoly_smooth : (algebraMap ℤ (Polynomial ℤ)).Smooth := by
  haveI : Algebra.FormallySmooth ℤ (Polynomial ℤ) :=
    inferInstance
  haveI : Algebra.Smooth ℤ (Polynomial ℤ) := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem laurent_smooth : (algebraMap ℤ (LaurentPolynomial ℤ)).Smooth := by
  have h2 : (algebraMap (Polynomial ℤ) (LaurentPolynomial ℤ)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (LaurentPolynomial ℤ) (Polynomial.X : Polynomial ℤ)
  have := RingHom.Smooth.comp intPoly_smooth h2
  convert this
  exact RingHom.ext_int _ _

theorem gm_from_smooth : Smooth (specZIsTerminal.from Gm) := by
  have e : specZIsTerminal.from Gm =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := specZIsTerminal.hom_ext _ _
  rw [e, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact laurent_smooth

theorem gmU_smooth (X : Scheme.{0}) : Smooth (prod.fst : X ⨯ Gm ⟶ X) := by
  have hp := IsPullback.of_is_product (limit.isLimit (pair X Gm)) specZIsTerminal
  have := gm_from_smooth
  exact MorphismProperty.of_isPullback (P := @Smooth) hp.flip this

theorem gmU_surj (X : Scheme.{0}) : Surjective (prod.fst : X ⨯ Gm ⟶ X) := by
  let pt : Spec (CommRingCat.of ℤ) ⟶ Gm :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1))
  let s : X ⟶ X ⨯ Gm := prod.lift (𝟙 X) (specZIsTerminal.from X ≫ pt)
  have hs : s ≫ prod.fst = 𝟙 X := prod.lift_fst _ _
  have : Surjective (s ≫ prod.fst) := by rw [hs]; infer_instance
  exact Surjective.of_comp s prod.fst

theorem LeafWGm_of : LeafWGm := fun _ _ _ _ => ⟨gmU_smooth _, gmU_surj _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

