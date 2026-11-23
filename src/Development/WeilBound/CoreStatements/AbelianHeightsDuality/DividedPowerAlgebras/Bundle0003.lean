module

public import Mathlib
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0001
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.AcycOfCoprod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsDPMorphismId
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}}

def NT (κ : DividedPowers I) {s : X ⟶ Sp R} {K : Type} (U : K → X.Opens) : ObjectProperty (Tag (dp0 R) s U) :=
  fun S ↦ InN κ S.T

theorem isDPMorphism_id {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism

structure Red (κ : DividedPowers I) {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀)
    (i : X₀ ⟶ X) : Prop where
  nil : IsNilDP κ
  surj : Function.Surjective π
  ker : RingHom.ker π = I
  pb : IsPullback i s₀ s (spMap π)

variable {κ : DividedPowers I} {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀}
  {i : X₀ ⟶ X} (h : Red κ π s s₀ i)

namespace Red

include h

theorem mor : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i := by
  refine IsMor.of_dividedPowersZeroIdeal κ ?_
  rw [GlobalTheory.Cris.spMap_id, Category.comp_id]
  exact h.pb.w

theorem surjective : Function.Surjective i := by
  have hnil : ∀ x ∈ I, ∃ N : ℕ, x ^ N = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := h.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x))
      (by
        intro p hp
        rw [List.eq_of_mem_replicate hp]
        exact hx)
      (by simp)
    simpa [List.map_replicate, List.prod_replicate, κ.dpow_one hx] using this
  have hsurj : Function.Surjective (spMap π) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap π) := by
      open PrimeSpectrum in rw [range_comap_of_surjective _ π h.surj, h.ker]
      change (I : Set R) ⊆ (p : PrimeSpectrum R).asIdeal
      intro x hx
      obtain ⟨N, hN⟩ := hnil x hx
      exact p.isPrime.mem_of_pow_mem N (by rw [hN]; exact p.asIdeal.zero_mem)
    exact hp
  have hS : AlgebraicGeometry.Surjective (spMap π) := (AlgebraicGeometry.surjective_iff _).mpr hsurj
  exact (AlgebraicGeometry.surjective_iff i).mp
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h.pb.flip hS)

theorem le_of_le {U V : X.Opens} (e : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) : U ≤ V := by
  intro x hx
  obtain ⟨y, rfl⟩ := h.surjective x
  exact (show y ∈ i ⁻¹ᵁ V from e (show y ∈ i ⁻¹ᵁ U from hx))

theorem inN_obj (T : Thick κ (s₀ ≫ spMap π)) : InN κ (h.mor.obj T) := by
  show ∃ δ' : DividedPowers (T.J ⊔ Ideal.map (algebraMap R T.B) I),
    T.δ.IsDPMorphism δ' (RingHom.id T.B) ∧ κ.IsDPMorphism δ' (algebraMap R T.B)
  rw [sup_eq_left.mpr T.dp.ideal_comp]
  exact ⟨T.δ, isDPMorphism_id T.δ, T.dp⟩

end Red

section Up

variable (S : Thick (dp0 R) s)

abbrev big (I : Ideal R) : Ideal S.B := S.J ⊔ I.map (algebraMap R S.B)

def rho (I : Ideal R) : S.B₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective S.π S.surj ⟨Ideal.Quotient.mk _, fun b hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ((S.ker b).1 hb))⟩

theorem rho_π (I : Ideal R) (b : S.B) : rho S I (S.π b) = Ideal.Quotient.mk _ b :=
  RingHom.liftOfSurjective_comp_apply _ _ _ b

def Red.sig : R₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective π h.surj ⟨(Ideal.Quotient.mk _).comp (algebraMap R S.B), fun r hr ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (h.ker ▸ hr)))⟩

theorem Red.sig_π (r : R) : h.sig S (π r) = Ideal.Quotient.mk _ (algebraMap R S.B r) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ r

def Red.pt : Sp (S.B ⧸ big S I) ⟶ X₀ :=
  h.pb.lift (spMap (rho S I) ≫ S.x) (spMap (h.sig S)) (by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ (rho_π S I _).trans (h.sig_π S r).symm)

theorem Red.pt_i : h.pt S ≫ i = spMap (rho S I) ≫ S.x := h.pb.lift_fst _ _ _

theorem Red.pt_s : h.pt S ≫ s₀ = spMap (h.sig S) := h.pb.lift_snd _ _ _

@[reducible] def Red.up (hS : InN κ S) : Thick κ (s₀ ≫ spMap π) where
  B := S.B
  J := big S I
  δ := hS.choose
  nil := nil_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 h.nil S.nil
  dp := hS.choose_spec.2
  B₀ := S.B ⧸ big S I
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := h.pt S
  w := by
    rw [← Category.assoc, h.pt_s, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ h.sig_π S r

variable {S}

def Red.rh {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : S.B →+* T.B :=
  (f.φ : S.B →+* (h.mor.obj T).B)

theorem Red.rh_algebraMap {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) (r : R) :
    h.rh f (algebraMap R S.B r) = algebraMap R T.B r := f.φ.commutes r

def Red.upTo (hS : InN κ S) {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : h.up S hS ⟶ T where
  φ := { (h.rh f) with commutes' := h.rh_algebraMap f }
  φ₀ := Ideal.Quotient.lift _ (T.π.comp (h.rh f)) fun b hb ↦ (T.ker _).2 (by
    have : big S I ≤ T.J.comap (h.rh f) := sup_le (fun b hb ↦ f.mem hb)
      (Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
        change h.rh f (algebraMap R S.B r) ∈ T.J
        rw [h.rh_algebraMap]
        exact T.dp.1 (Ideal.mem_map_of_mem _ hr))
    exact this hb)
  comm _ := rfl
  dp := isDPMorphism_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 T.δ _ f.dp (by
    change IsDPMorphism κ T.δ ((h.rh f).comp (algebraMap R S.B))
    rw [show (h.rh f).comp (algebraMap R S.B) = algebraMap R T.B from RingHom.ext (h.rh_algebraMap f)]
    exact T.dp)
  pt := by
    refine h.pb.hom_ext ?_ ?_
    · change (_ ≫ h.pt S) ≫ i = _
      rw [Category.assoc, h.pt_i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
      refine Eq.trans ?_ f.pt
      congr 2
      refine RingHom.ext fun b ↦ ?_
      obtain ⟨b, rfl⟩ := S.surj b
      rw [RingHom.comp_apply, rho_π]
      exact (f.comm b).symm
    · change (_ ≫ h.pt S) ≫ s₀ = _
      have : Mono (spMap π) := by
        have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ h.surj
        infer_instance
      rw [← cancel_mono (spMap π), Category.assoc, Category.assoc, ← Category.assoc (h.pt S), h.pt_s,
        Category.assoc, T.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
      congr 1
      refine RingHom.ext fun r ↦ ?_
      simp only [RingHom.comp_apply]
      rw [h.sig_π]
      exact congrArg T.π (h.rh_algebraMap f r)

def Red.unit (hS : InN κ S) : S ⟶ h.mor.obj (h.up S hS) where
  φ := { RingHom.id S.B with commutes' := fun _ ↦ rfl }
  φ₀ := rho S I
  comm := rho_π S I
  dp := hS.choose_spec.1
  pt := (h.pt_i S).symm

end Up

variable {K : Type} (U : K → X.Opens)

abbrev redOpen (i : X₀ ⟶ X) : K → X₀.Opens := fun k ↦ i ⁻¹ᵁ U k

def Red.G : Tag κ (s₀ ≫ spMap π) (redOpen U i) ⥤ (NT κ U (s := s)).FullSubcategory where
  obj T := ⟨⟨h.mor.obj T.T, T.k, T.le⟩, h.inN_obj T.T⟩
  map f := ObjectProperty.homMk (⟨h.mor.functor.map (Tag.Hom.f f), h.le_of_le (Tag.Hom.le f)⟩ : Tag.Hom _ _)
  map_id _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))
  map_comp _ _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))

def Red.H : (NT κ U (s := s)).FullSubcategory ⥤ Tag κ (s₀ ≫ spMap π) (redOpen U i) where
  obj S := ⟨h.up S.obj.T S.property, S.obj.k, (h.unit S.property).le_preimage S.obj.le⟩
  map {S S'} f := ⟨h.upTo S.property (Tag.Hom.f f.hom ≫ h.unit S'.property),
    fun _ hp ↦ Tag.Hom.le f.hom hp⟩
  map_id _ := Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl))
  map_comp f g := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b) = (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b))

abbrev FN (κ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    (NT κ U (s := s)).FullSubcategory ⥤ CommAlgCat.{0} R :=
  (NT κ U).ι ⋙ Tag.forget (dp0 R) s U ⋙ O (dp0 R) s

def Red.cG : CoefMap (RingHom.id R) (FN κ s U) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) where
  G := h.G U
  α T := RingHom.id T.T.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.T.B) r b).symm

def Red.cH : CoefMap (RingHom.id R) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) (FN κ s U) where
  G := h.H U
  α S := RingHom.id S.obj.T.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def Red.η : 𝟭 _ ⟶ h.H U ⋙ h.G U where
  app S := ObjectProperty.homMk
    (⟨h.unit S.property, le_rfl⟩ : Tag.Hom S.obj ((h.G U).obj ((h.H U).obj S)).obj)
  naturality S S' f := by
    refine ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)))
    exact (rfl : (Tag.Hom.f f.hom).φ b = (Tag.Hom.f f.hom).φ b)

def Red.ε : h.G U ⋙ h.H U ⟶ 𝟭 _ where
  app T := (⟨h.upTo (h.inN_obj T.T) (𝟙 _), le_rfl⟩ : Tag.Hom ((h.H U).obj ((h.G U).obj T)) T)
  naturality S S' f := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f f).φ b = (Tag.Hom.f f).φ b)

theorem Red.cG_pull1 : Function.Bijective (h.cG U).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact ((CoefMap.id _).pullCohomologyOne_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyOne_id c)
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyOne_id c)

theorem Red.cG_pull2 : Function.Bijective (h.cG U).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact ((CoefMap.id _).pullCohomologyTwo_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c)
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyTwo_id c)

end FubiniStudyChowHeightFormula₂.Adr
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.TagIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u' v'' u''

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']

theorem restrict_pull1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H1 F) :
    (CoefMap.restrict (G ⋙ F) H).pull1 ((CoefMap.restrict F G).pull1 c) =
      (CoefMap.restrict F (H ⋙ G)).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

theorem restrict_pull2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H2 F) :
    (CoefMap.restrict (G ⋙ F) H).pull2 ((CoefMap.restrict F G).pull2 c) =
      (CoefMap.restrict F (H ⋙ G)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

end General

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

def toSmall (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    Tag γ s U ⥤ (IsSmall γ s U).FullSubcategory where
  obj S := ⟨S.T, S.k, S.le⟩
  map f := ⟨f.f⟩

section Comma

variable {T : (IsSmall γ s U).FullSubcategory}

theorem comma_le (a : CostructuredArrow (toSmall γ s U) T) : ⊤ ≤ T.obj.x ⁻¹ᵁ U a.left.k :=
  Thick.Hom.le_preimage a.hom.hom a.left.le

def selfObj (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k) : CostructuredArrow (toSmall γ s U) T :=
  CostructuredArrow.mk (Y := (⟨T.obj, k, h⟩ : Tag γ s U)) (𝟙 T)

def toSelf (a : CostructuredArrow (toSmall γ s U) T) (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k)
    (e : U a.left.k ≤ U k) : a ⟶ selfObj k h :=
  CostructuredArrow.homMk (⟨a.hom.hom, e⟩ : Tag.Hom _ _) (Category.comp_id _)

theorem toSelf_unique {a : CostructuredArrow (toSmall γ s U) T} {k : K} {h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k}
    (f g : a ⟶ selfObj k h) : f = g := by
  have hf := CostructuredArrow.w f
  have hg := CostructuredArrow.w g
  apply CostructuredArrow.hom_ext
  revert hf hg
  rcases f with ⟨⟨f1, l1⟩, fr, fw⟩
  rcases g with ⟨⟨g1, l2⟩, gr, gw⟩
  intro hf hg
  simp [selfObj, toSmall] at hf hg ⊢
  have e : f1 = g1 := congrArg (fun q => q.hom) (hf.trans hg.symm)
  subst e
  rfl

def selfFun (m : CostructuredArrow (toSmall γ s U) T → K) (h : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m a))
    (mono : ∀ a b, (a ⟶ b) → U (m a) ≤ U (m b)) :
    CostructuredArrow (toSmall γ s U) T ⥤ CostructuredArrow (toSmall γ s U) T where
  obj a := selfObj (m a) (h a)
  map {a b} f := toSelf _ _ _ (mono a b f)
  map_id _ := toSelf_unique _ _
  map_comp _ _ := toSelf_unique _ _

private theorem pull1_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull1 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull1 c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull2_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull2 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull2 c :=
  CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull1_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H1 F) : (CoefMap.restrict F (𝟭 D)).pull1 c = c := by
  have e := CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyOne_id] at e
  exact e.symm

private theorem pull2_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H2 F) : (CoefMap.restrict F (𝟭 D)).pull2 c = c := by
  have e := CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyTwo_id] at e
  exact e.symm

private theorem H2_discrete_punit_eq_zero (F : Discrete PUnit.{1} ⥤ CommAlgCat.{0} R) (c : GlobalTheory.CatCoh.H2 F) :
    c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [H2.mk_eq_zero]
  refine ⟨fun a b φ => z.1 a b b φ (𝟙 b), ?_⟩
  funext a b d φ ψ
  rcases a with ⟨⟨⟩⟩
  rcases b with ⟨⟨⟩⟩
  rcases d with ⟨⟨⟩⟩
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : ψ = 𝟙 _ := Subsingleton.elim _ _
  simp [d1_apply, mp]

private theorem pull1_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull1 c = 0 := by
  have e := restrict_pull1 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H1.eq_zero_of_isInitial _ (T₀ := (⟨⟨⟩⟩ : Discrete PUnit.{1}))
    (Limits.IsInitial.ofUniqueHom (fun _ => Discrete.eqToHom (Subsingleton.elim _ _))
      (fun _ _ => Subsingleton.elim _ _))
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull1 c),
    map_zero] at e
  exact e.symm

private theorem pull2_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull2 c = 0 := by
  have e := restrict_pull2 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H2_discrete_punit_eq_zero _
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull2 c),
    map_zero] at e
  exact e.symm

theorem acyc_toSmall (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) (T : (IsSmall γ s U).FullSubcategory) :
    Acyc R (CostructuredArrow (toSmall γ s U) T) := by
  obtain ⟨k0, h0⟩ := T.property
  choose m2 hm2 using fun (a : CostructuredArrow (toSmall γ s U) T) => hinf a.left.k k0
  have h2 : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m2 a) := by
    intro a
    rw [hm2 a]
    intro p hp
    exact ⟨comma_le a hp, h0 hp⟩
  let S1 := selfFun (T := T) (fun a => a.left.k) comma_le (fun a b f => Tag.Hom.le f.left)
  let S2 := selfFun (T := T) m2 h2 (fun a b f => by
    rw [hm2 a, hm2 b]
    exact inf_le_inf_right _ (Tag.Hom.le f.left))
  let θ1 : 𝟭 _ ⟶ S1 :=
    { app := fun a => toSelf a _ (comma_le a) le_rfl
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ2 : S2 ⟶ S1 :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) a.left.k (comma_le a)
        (show U (m2 a) ≤ U a.left.k by rw [hm2 a]; exact inf_le_left)
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ3 : S2 ⟶ (Functor.const _).obj (selfObj k0 h0) :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) k0 h0
        (show U (m2 a) ≤ U k0 by rw [hm2 a]; exact inf_le_right)
      naturality := fun _ _ _ => toSelf_unique (k := k0) (h := h0) _ _ }
  refine ⟨⟨selfObj k0 h0⟩, fun M => ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    have key : ∀ a, g a = g (selfObj k0 h0) := fun a =>
      (hg _ _ (θ1.app a)).symm.trans ((hg _ _ (θ2.app a)).trans (hg _ _ (θ3.app a)).symm)
    intro a b
    exact (key a).trans (key b).symm
  · intro c
    exact (pull1_restrict_id _ c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull1_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull1_restrict_const_const_eq_zero M _ c))))
  · intro c
    exact (pull2_restrict_id _ c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull2_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull2_restrict_const_const_eq_zero M _ c))))

end Comma

theorem tag_pull1 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull1 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull1 :=
    funext fun c => (restrict_pull1 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa1 _ _ (fun T => acyc_toSmall hinf T)).comp
    (SmallDescent.pull1_bijective R I γ X s K U hcov)

private theorem pull2_restrict_isSmall_bijective_of_cover (hcov : ⨆ k, U k = ⊤) :
    Function.Bijective (CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 := by
  apply Desc.pull2_bijective
  · intro T b
    obtain ⟨L, l, hl⟩ := SmallDescent.exists_isLoc T b
    obtain ⟨hu, hsurj, hker, hfac⟩ := hl
    refine ⟨L, l, hu, ?_, hker, ?_⟩
    · intro y
      obtain ⟨n, N, h⟩ := hsurj y
      exact ⟨N, n, h⟩
    · intro S u hu'
      obtain ⟨ψ, hψ⟩ := hfac S u hu'
      exact ⟨ψ, hψ, fun ψ' h' =>
        SmallDescent.IsLoc.hom_ext ⟨hu, hsurj, hker, hfac⟩ (h'.trans hψ.symm)⟩
  · intro S S' a hS
    exact SmallDescent.isSmall_of_hom a hS
  · intro T
    obtain ⟨σ, hσ, hσs⟩ := SmallDescent.exists_cover hcov T
    refine ⟨σ.card, fun i => (σ.equivFin.symm i : T.B), ?_, ?_⟩
    · have hr : Set.range (fun i => (σ.equivFin.symm i : T.B)) = (σ : Set T.B) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact (σ.equivFin.symm i).2
        · intro hx
          exact ⟨σ.equivFin ⟨x, hx⟩, by simp⟩
      rw [hr]
      exact hσ
    · intro i S u hu
      exact hσs _ (σ.equivFin.symm i).2 S u hu

theorem tag_pull2 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull2 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 :=
    funext fun c => (restrict_pull2 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa2 _ _ (fun T => acyc_toSmall hinf T)).comp (pull2_restrict_isSmall_bijective_of_cover hcov)

end FubiniStudyChowHeightFormula₂.Adr
end
end

