module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CechFamily
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)
  {P P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

structure CechFamily (P P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) where

  φ : ∀ {n : ℕ} (i : Fin (n + 1) → ι), P.obj (op (inter U i)) →+ P'.obj (op (inter U i))

  res_comm : ∀ {m n : ℕ} (i : Fin (m + 1) → ι) (j : Fin (n + 1) → ι) (h : inter U i ≤ inter U j)
    (x : P.obj (op (inter U j))), φ i (res P h x) = res P' h (φ j x)

namespace CechFamily

variable {U}

noncomputable section

def cochain (Φ : CechFamily U P P') (n : ℕ) : Cochain P U n →+ Cochain P' U n where
  toFun σ i := Φ.φ i (σ i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' σ τ := by
    funext i
    exact map_add _ _ _

lemma cochain_apply (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    Φ.cochain n σ i = Φ.φ i (σ i) := rfl

lemma cochain_d (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) :
    Φ.cochain (n + 1) (d P U n σ) = d P' U n (Φ.cochain n σ) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cochain_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Φ.res_comm]
  rfl

lemma cochain_mem_cocycles (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ cocycles P U n) : Φ.cochain n σ ∈ cocycles P' U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← cochain_d, hσ, map_zero]

lemma cochain_mem_coboundaries (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ coboundaries P U n) : Φ.cochain n σ ∈ coboundaries P' U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨Φ.cochain n τ, (cochain_d Φ n τ).symm⟩

def cocycles (Φ : CechFamily U P P') (n : ℕ) : cocycles P U n →+ GroundTheory.Arith.SchemeCoh.cocycles P' U n :=
  AddMonoidHom.codRestrict ((Φ.cochain n).comp (GroundTheory.Arith.SchemeCoh.cocycles P U n).subtype) _
    fun σ => cochain_mem_cocycles Φ σ.2

def cechH (Φ : CechFamily U P P') (n : ℕ) : GroundTheory.Arith.SchemeCoh.cechH P U n →+
    GroundTheory.Arith.SchemeCoh.cechH P' U n :=
  QuotientAddGroup.map _ _ (Φ.cocycles n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact cochain_mem_coboundaries Φ (AddSubgroup.mem_addSubgroupOf.1 hσ)

lemma cechH_cls (Φ : CechFamily U P P') {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    Φ.cechH n (cls σ hσ) = cls (Φ.cochain n σ) (by rw [← cochain_d, hσ, map_zero]) := rfl

def ofHom (f : P ⟶ P') : CechFamily U P P' where
  φ i := (f.app (op (inter U i))).hom
  res_comm i j h x := app_res f h x

lemma ofHom_cechH (f : P ⟶ P') (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (ofHom (U := U) f).cechH n x = cechHMap U f n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechH_cls, cechHMap_cls]
  exact cls_congr U (by funext i; rfl) _ _

def comp (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') : CechFamily U P P'' where
  φ i := (Ψ.φ i).comp (Φ.φ i)
  res_comm i j h x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [Φ.res_comm, Ψ.res_comm]

lemma comp_cechH (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') (n : ℕ)
    (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (Φ.comp Ψ).cechH n x = Ψ.cechH n (Φ.cechH n x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rfl

lemma cechH_congr {Φ Ψ : CechFamily U P P'} (h : ∀ {n : ℕ} (i : Fin (n + 1) → ι) x, Φ.φ i x = Ψ.φ i x)
    (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) : Φ.cechH n x = Ψ.cechH n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechH_cls, cechH_cls]
  exact cls_congr U (by funext i; exact h i _) _ _

end

end CechFamily

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A]

abbrev chartStructureMap (n : ℕ) : A →+* Chart A (0 : Fin (n + 1)) :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))

lemma chartToPoly_chartStructureMap (n : ℕ) (a : A) :
    chartToPoly A (0 : Fin (n + 1)) (chartStructureMap n a) = C a := by
  have h : chartStructureMap (A := A) n a = polyToChart A 0 (C a) := by
    simp [polyToChart]
  rw [h, ← RingHom.comp_apply, chartToPoly_polyToChart, RingHom.id_apply]

theorem exists_surjective_chart {B : Type u} [CommRing B] (ρ : A →+* B) (hρ : ρ.FiniteType) :
    ∃ (n : ℕ) (g : Chart A (0 : Fin (n + 1)) →+* B), Function.Surjective g ∧
      g.comp (chartStructureMap n) = ρ := by
  let _ := ρ.toAlgebra
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hρ
  let ψ : MvPolynomial {j : Fin (n + 1) // j ≠ 0} A →+* B :=
    eval₂Hom ρ fun j => s (X (j.1.pred j.2))
  let e : Fin n → {j : Fin (n + 1) // j ≠ 0} := fun k => ⟨k.succ, Fin.succ_ne_zero k⟩
  have hψ : ∀ p, ψ (rename e p) = s p := by
    intro p
    rw [MvPolynomial.aeval_unique s]
    simp only [ψ, coe_eval₂Hom, eval₂_rename, e, aeval_def]
    rfl
  refine ⟨n, ψ.comp (chartToPoly A 0), ?_, ?_⟩
  · intro b
    obtain ⟨p, rfl⟩ := hs b
    obtain ⟨z, hz⟩ := (chartEquiv A (0 : Fin (n + 1))).surjective (rename e p)
    exact ⟨z, by rw [RingHom.comp_apply]; change ψ (chartEquiv A 0 z) = _; rw [hz, hψ]⟩
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, chartToPoly_chartStructureMap]
    simp [ψ]

theorem exists_closedImmersion_stdOpen {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (c : U.toScheme ⟶ (stdOpen A n 0).toScheme), IsClosedImmersion c ∧
      c ≫ (stdOpen A n 0).ι ≫ toSpecBase A n = U.ι ≫ f := by
  let ρ' : CommRingCat.of A ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U le_top
  have hρ : ρ'.hom.FiniteType := by
    refine RingHom.FiniteType.comp (f.finiteType_appLE (isAffineOpen_top _) hU le_top) ?_
    exact RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2
  obtain ⟨n, g, hg, hgc⟩ := exists_surjective_chart ρ'.hom hρ
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 := X_mem 0
  let c : U.toScheme ⟶ (Proj.basicOpen (grading A n) (MvPolynomial.X 0)).toScheme :=
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading A n) (MvPolynomial.X 0) hX0 one_pos).inv
  have hc : IsClosedImmersion c := by
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
    dsimp only [c]
    infer_instance
  refine ⟨n, c, hc, ?_⟩
  have h1 : U.ι ≫ f = hU.isoSpec.hom ≫ Spec.map ρ' := by
    rw [← hU.isoSpec_hom_fromSpec, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec, asIso_inv]
    congr 1
    rw [IsIso.comp_inv_eq, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    congr 1
    simp [ρ']
  rw [h1]
  change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
      ((Proj.basicOpenIsoSpec (grading A n) (MvPolynomial.X 0) hX0 one_pos).inv ≫
        (Proj.basicOpen (grading A n) (MvPolynomial.X 0)).ι) ≫ toSpecBase A n = _
  rw [Proj.basicOpenIsoSpec_inv_ι, toSpecBase, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  change g (chartStructureMap n a) = ρ'.hom a
  rw [← RingHom.comp_apply, hgc]

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

lemma irrelevant_le_span_X (A : Type u) [CommRing A] (n : ℕ) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A)) := by
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)

def gradedMap : grading A n →+*ᵍ grading B n where
  toRingHom := MvPolynomial.map (algebraMap A B)
  map_mem {_ _} hx :=
    (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hx).map _)

lemma gradedMap_apply (p : MvPolynomial (Fin (n + 1)) A) :
    gradedMap A B n p = MvPolynomial.map (algebraMap A B) p := rfl

@[simp] lemma gradedMap_X (j : Fin (n + 1)) : gradedMap A B n (X j) = X j := by
  simp [gradedMap_apply]

lemma irrelevant_le_map :
    HomogeneousIdeal.irrelevant (grading B n) ≤
      (HomogeneousIdeal.irrelevant (grading A n)).map (gradedMap A B n) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (irrelevant_le_span_X B n).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨j, rfl⟩
  rw [← gradedMap_X A B n j]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem j))

def baseChangeMap : projectiveSpace B n ⟶ projectiveSpace A n :=
  Proj.map (gradedMap A B n) (irrelevant_le_map A B n)

def stdAffineCover (A : Type u) [CommRing A] (n : ℕ) : (projectiveSpace A n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading A n)
    (fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) A)) (fun j => X_mem j)
    (fun _ => Nat.one_pos) (irrelevant_le_span_X A n)

def chartAlgebraMap (A : Type u) [CommRing A] {n : ℕ} (s : MvPolynomial (Fin (n + 1)) A) :
    A →+* Away (grading A n) s :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))

def awayCongr {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    Away (grading B n) s ≃+* Away (grading B n) t := by
  subst h
  exact RingEquiv.refl _

lemma awayCongr_mk {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) {d : ℕ}
    (hs : s ∈ grading B n d) (ht : t ∈ grading B n d) (m : ℕ) (x : MvPolynomial (Fin (n + 1)) B)
    (hx : x ∈ grading B n (m • d)) :
    awayCongr B n h (Away.mk (grading B n) hs m x hx) = Away.mk (grading B n) ht m x hx := by
  subst h
  rfl

lemma awayCongr_chartAlgebraMap {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) (b : B) :
    awayCongr B n h (chartAlgebraMap B s b) = chartAlgebraMap B t b := by
  subst h
  rfl

variable {A B n}

lemma map_chartAlgebraMap (j : Fin (n + 1)) (a : A) :
    Away.map (gradedMap A B n) (X j) (chartAlgebraMap A (X j) a) =
      chartAlgebraMap B (gradedMap A B n (X j)) (algebraMap A B a) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = Localization.mk _ _
  congr 1
  · simp [gradedMap_apply, MvPolynomial.algebraMap_eq]
  · ext
    simp [gradedMap_apply]

lemma awayCongr_symm {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    (awayCongr B n h).symm = awayCongr B n h.symm := by
  subst h
  rfl

lemma chartEquiv_symm_apply (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    (chartEquiv A j).symm p = polyToChart A j p := rfl

lemma polyToChart_C (j : Fin (n + 1)) (a : A) :
    polyToChart A j (C a) = chartAlgebraMap A (X j) a := by
  simp [polyToChart, chartAlgebraMap]

lemma map_polyToChart (j : Fin (n + 1)) :
    (Away.map (gradedMap A B n) (X j)).comp (polyToChart A j) =
      ((awayCongr B n (gradedMap_X A B n j)).symm.toRingHom.comp (polyToChart B j)).comp
        (MvPolynomial.map (algebraMap A B)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, map_C, polyToChart_C, map_chartAlgebraMap,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCongr_symm, awayCongr_chartAlgebraMap]
  · intro k
    simp only [RingHom.comp_apply, map_X, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      awayCongr_symm, polyToChart, coe_eval₂Hom, eval₂_X, coordinate, Away.map_mk]
    rw [awayCongr_mk B n _ (X_mem j) (by rw [gradedMap_X]; exact X_mem j)]
    apply HomogeneousLocalization.val_injective
    simp [Away.val_mk]

lemma map_polyToChart_apply (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    Away.map (gradedMap A B n) (X j) (polyToChart A j p) =
      (awayCongr B n (gradedMap_X A B n j)).symm (polyToChart B j (MvPolynomial.map (algebraMap A B) p)) :=
  congrArg (fun φ => φ p) (map_polyToChart (A := A) (B := B) j)


attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem isPushout_chart (j : Fin (n + 1)) :
    IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (chartAlgebraMap A (X j)))
      (CommRingCat.ofHom (chartAlgebraMap B (gradedMap A B n (X j))))
      (CommRingCat.ofHom (Away.map (gradedMap A B n) (X j))) := by
  have h0 := CommRingCat.isPushout_of_isPushout A B (MvPolynomial {i // i ≠ j} A)
    (MvPolynomial {i // i ≠ j} B)
  refine h0.of_iso (Iso.refl _) (Iso.refl _) (chartEquiv A j).symm.toCommRingCatIso
    ((chartEquiv B j).symm.trans (awayCongr B n (gradedMap_X A B n j)).symm).toCommRingCatIso
    ?_ ?_ ?_ ?_
  · ext x
    rfl
  · ext x
    simp [chartEquiv_symm_apply, polyToChart_C]
  · ext x
    simp [chartEquiv_symm_apply, polyToChart_C, awayCongr_symm, awayCongr_chartAlgebraMap]
  · apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext <;> intro x <;>
      simp [chartEquiv_symm_apply, map_polyToChart_apply]


variable (A) in
lemma awayι_toSpecBase {s : MvPolynomial (Fin (n + 1)) A} {d : ℕ} (hs : s ∈ grading A n d)
    (hd : 0 < d) :
    Proj.awayι (grading A n) s hs hd ≫ toSpecBase A n =
      Spec.map (CommRingCat.ofHom (chartAlgebraMap A s)) := by
  rw [toSpecBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl


variable (A B n) in
theorem isPullback_baseChange :
    IsPullback (baseChangeMap A B n) (toSpecBase B n) (toSpecBase A n)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (stdAffineCover A n).openCover fun j => ?_
  have hQ : IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedMap A B n) (X j))))
      (Proj.awayι (grading B n) (gradedMap A B n (X j)) ((gradedMap A B n).2 (X_mem j)) Nat.one_pos)
      (Proj.awayι (grading A n) (X j : MvPolynomial (Fin (n + 1)) A) (X_mem j) Nat.one_pos)
      (baseChangeMap A B n) :=
    IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map _ _ _ _ _)
      (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι]; rfl)
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart (A := A) (B := B) (n := n) j)
  refine hS.flip.of_iso hQ.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact (hQ.flip.isoPullback_hom_snd).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = hQ.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ toSpecBase B n
    rw [hQ.flip.isoPullback_hom_fst_assoc, awayι_toSpecBase]
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (awayι_toSpecBase A (X_mem j) Nat.one_pos).symm
  · simp

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

