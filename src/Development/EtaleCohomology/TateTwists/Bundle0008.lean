module

public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainsMayerVietorisShortExactOfFree
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleFreePresheafMayerVietorisShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g],
    Mono (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g))) ∧
    ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g)))
      (biprod.desc ((free R).map f) ((free R).map g)) w).Exact

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    ((chains R).map φ).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom =
      (chainsXIso R E p).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk p))) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := p) (i' := -(p:ℤ)) rfl
  have h2 : ((chains R).map φ).f (-(p:ℤ)) = (HomologicalComplex.extendMap ((chainsN R).map φ) ComplexShape.embeddingDownNat).f (-(p:ℤ)) := rfl
  rw [h2, h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i:ℤ) = n at h
  omega

theorem chainsXIso_nat' (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map φ).f (-(p : ℤ)) =
      (free R).map (φ.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← chainsXIso_nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem sq1 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    ((free R).map (pullbackObjIso f g (op (SimplexCategory.mk p))).inv ≫ (chainsXIso R (pullback f g) p).inv) ≫
      (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))).f (-(p:ℤ)) =
    biprod.lift ((free R).map (pullback.fst (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))))
        (-(free R).map (pullback.snd (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))))) ≫
      (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) := by
  rw [← cancel_mono (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, chainsXIso_nat', ← Category.assoc, ← Functor.map_comp,
      pullbackObjIso_inv_comp_fst]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      chainsXIso_nat']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Category.assoc, ← Functor.map_comp, pullbackObjIso_inv_comp_snd]

theorem sq2 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) ≫
      (biprod.desc ((chains R).map f) ((chains R).map g)).f (-(p:ℤ)) =
    biprod.desc ((free R).map (f.app (op (SimplexCategory.mk p)))) ((free R).map (g.app (op (SimplexCategory.mk p)))) ≫
      (chainsXIso R E p).inv := by
  apply biprod.hom_ext'
  · have h1 : biprod.inl ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inl : (chains R).obj U ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inl_desc,
      chainsXIso_nat', biprod.inl_desc_assoc]
  · have h1 : biprod.inr ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inr : (chains R).obj V ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inr_desc,
      chainsXIso_nat', biprod.inr_desc_assoc]

theorem etale_chains_mayer_vietoris_short_exact_of_free (hfree : EtaleFreePresheafMayerVietorisShortExact) : EtaleMayerVietorisChainsShortExact := by
  intro R _ U V E f g hc
  obtain ⟨hf, hg, hep⟩ := hc
  have w : biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) ≫
      biprod.desc ((chains R).map f) ((chains R).map g) = 0 := by
    rw [biprod.lift_desc, ← Functor.map_comp, Preadditive.neg_comp, ← Functor.map_comp, pullback.condition]
    simp
  refine ⟨w, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : 0 < n
  · have h1 := chains_isZero R (pullback f g) n hn
    have h3 := chains_isZero R E n hn
    have h2 : IsZero ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n).obj
        ((chains R).obj U ⊞ (chains R).obj V)) := by
      have hU := chains_isZero R U n hn
      have hV := chains_isZero R V n hn
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ n)
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hU.eq_of_tgt biprod.fst 0, hV.eq_of_tgt biprod.snd 0]
      simp
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h2) ?_ ?_
    · exact ⟨fun a b _ => h1.eq_of_tgt a b⟩
    · exact ⟨fun a b _ => h3.eq_of_src a b⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  obtain ⟨hmono, w', hex⟩ := hfree R (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))
  have hT := ShortComplex.ShortExact.mk' hex hmono (hep _)
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk ?e1 ?e2 ?e3 ?c1 ?c2
  case e1 =>
    refine ?_ ≪≫ (chainsXIso R _ p).symm
    exact (free R).mapIso (pullbackObjIso f g _).symm
  case e2 => exact biprod.mapIso (chainsXIso R U p).symm (chainsXIso R V p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ _).symm
  case e3 => exact (chainsXIso R E p).symm
  case c1 => exact sq1 R f g p
  case c2 => exact sq2 R f g p

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupCompatibleWithCoefficientMapsOfSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCupCompatAlexanderWhitneyCocycleSpec : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

theorem etale_cochain_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (add_zero n) (-(p : ℤ)) s s h (add_zero s), Cochain.ofHom_v]
  rfl

theorem etale_cocycle_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (zcomp α (Cocycle.ofHom m) (add_zero n)).1 p s h U x =
      Sec.map (m.f s) (ev α.1 p s h U x) :=
  etale_cochain_comp_hom_evaluation_eq_map m α.1 p s h U x

theorem etale_cup_compatible_with_coefficient_maps_of_spec (hspec : EtaleCupCompatAlexanderWhitneyCocycleSpec) : EtaleCupProductNaturalInCoefficients := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, hγ⟩ := (hspec R μ hk).1 α β
  rw [(hspec R μ hk).2 α β γ hγ, cpost_mk, cpost_mk, cpost_mk]
  symm
  apply (hspec R ν hk).2
  intro N w h U x
  rw [etale_cocycle_comp_hom_evaluation_eq_map, hγ N w h U x]
  simp only [Sec.map]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, etale_cocycle_comp_hom_evaluation_eq_map, etale_cocycle_comp_hom_evaluation_eq_map]
  congr 1
  exact hc U _ _ w _ _ _

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FreeHomPf

variable (R : Type) [CommRing R]

noncomputable def desc (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : uliftFunctor.{1}.obj (P.obj U) => a U.unop x.down)
  naturality U W g := by
    apply ModuleCat.free_hom_ext
    intro x
    have := ha W.unop U.unop g.unop x.down
    simp only [Sec.res] at this
    simp only [freeP] at *
    simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.whiskeringRight_obj_map,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

lemma freePresheaf_map_generator {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (f.app (op U) x)) : ((freeP R).obj Q).obj (op U)) :=
  ModuleCat.free_map_apply _ _

lemma freePresheaf_obj_map_generator (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (P.map g.op x)) : ((freeP R).obj P).obj (op V)) :=
  ModuleCat.free_map_apply _ _

lemma gen_eq (P : PSh) (F : Shv R) (φ : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map φ (freeGen R P U x) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ φ.hom).app (op U)).hom
        (ModuleCat.freeMk (ULift.up x)) := rfl

end LateralTheory.EtaleFoundations.FreeHomPf

open LateralTheory.EtaleFoundations.FreeHomPf in
theorem LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  intro R _ P F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨⟨sheafifyLift Scheme.etaleTopology (desc R P F a ha) F.property⟩, fun U x => ?_⟩
    refine (gen_eq R P F _ U x).trans ?_
    rw [toSheafify_sheafifyLift]
    exact ModuleCat.freeDesc_apply _ _
  · intro φ ψ h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Scheme.etaleTopology _ _ F.property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    have := h U.unop x.down
    rw [gen_eq, gen_eq] at this
    exact this
  · intro V U g x
    have hn := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op)).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).obj P).map g.op ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
            ((((freeP R).obj P).map g.op).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_obj_map_generator]; rfl
  · intro Q f U x
    have hn := congrArg (fun η => η.app (op U))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).map f).app (op U) ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by
              simp only [NatTrans.comp_app] at hn; rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
            ((((freeP R).map f).app (op U)).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_map_generator]; rfl
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def kum_exists : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_nat : Prop :=
  ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def kum_add : Prop :=
  ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

theorem kum_spec_of_exists (he : kum_exists) (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ)
    (hq : IsUnit (q : Γ(X, ⊤))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v) := by
  obtain ⟨γ, h1, h2⟩ := he q X u hq
  unfold kum
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk γ = c ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    ⟨CohomologyClass.mk γ, γ, rfl, h1, h2⟩

theorem etale_kummer_class_specification_of_existence_naturality_additivity (he : kum_exists) (hn : kum_nat) (ha : kum_add) : EtaleKummerClassExplicitCocycle := by
  intro q _
  exact ⟨fun X u hq => kum_spec_of_exists he q X u hq, fun f u hq => hn q f u hq, fun u v hq => ha q u v hq⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
end

