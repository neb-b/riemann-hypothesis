module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

def sc {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def valR {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) : Γ(X, U) →+* O :=
  (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.comp (a.appLE U ⊤ h).hom

theorem top_le_of_closedPoint {O : Type} [CommRing O] [IsLocalRing O] (V : (Sp O).Opens)
    (h : IsLocalRing.closedPoint O ∈ V) : ⊤ ≤ V := by
  intro x _
  have hs : (x : Sp O) ⤳ IsLocalRing.closedPoint O :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum O).2.ne_top)
  exact hs.mem_open V.2 h

theorem valR_isUnit_iff {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (b : Γ(X, U)) :
    IsUnit (valR a U h b) ↔ a (IsLocalRing.closedPoint O) ∈ X.basicOpen b := by
  have e : (a.appLE U ⊤ h).hom b = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (valR a U h b) := by
    simp [valR]
  have e2 := Scheme.basicOpen_appLE a ⊤ U h b
  rw [e, basicOpen_eq_of_affine] at e2
  have : a (IsLocalRing.closedPoint O) ∈ X.basicOpen b ↔ IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b := Iff.rfl
  rw [this]
  have e3 : (IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b) ↔ (IsLocalRing.closedPoint O ∈ (PrimeSpectrum.basicOpen (valR a U h b))) := by
    rw [e2]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [e3]
  change _ ↔ (valR a U h b) ∉ IsLocalRing.maximalIdeal O
  simp [IsLocalRing.mem_maximalIdeal]

theorem valR_res {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR a V h ((X.presheaf.map (homOfLE hVU).op).hom f) = valR a U h' f := by
  simp only [valR, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_sc {O R : Type} [CommRing O] [CommRing R] {X : Scheme.{0}} (a : Sp O ⟶ X) (π : X ⟶ Sp R) (ρ : R →+* O)
    (hρ : a ≫ π = spMap ρ) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) (r : R) : valR a U h (sc π U r) = ρ r := by
  have key : ∀ (g : Sp O ⟶ Sp R) (_ : g = spMap ρ) (e : ⊤ ≤ g ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ρ r := by
    rintro _ rfl e
    have e1 : (spMap ρ).appLE ⊤ ⊤ e = (spMap ρ).appTop := Scheme.Hom.appLE_eq_app (f := spMap ρ) (U := ⊤)
    have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)
    rw [e1]
    have e3 : ((spMap ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (ρ r) :=
      (congrArg (fun q => q.hom r) e2).symm
    rw [e3]
    simp
  have e1 := Scheme.Hom.appLE_comp_appLE a π ⊤ U ⊤ (fun _ _ => trivial) h
  rw [← key (a ≫ π) hρ (by simpa using fun _ _ => trivial)]
  simp only [valR, sc, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, e1]

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC

open GlobalTheory.CompanionTheory.Ar.TorusModel

theorem pt_ext {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap e) φ) {T : Over (Sp L')} (u v : T ⟶ G')
    (huv : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext huv (by rw [Over.w u, Over.w v]))

theorem isTanAt_comp {S : Scheme.{0}} {R : Type} [CommRing R] {H G : Over S} [GrpObj H] [GrpObj G] (i : H ⟶ G)
    [IsMonHom i] (x : Sp R ⟶ S) (v : epsAt x ⟶ H) (hv : IsTanAt H x v) : IsTanAt G x (v ≫ i) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem dualMap_cast {L L' : Type} [Field L] [Field L'] (e : L →+* L') (n : ℤ) :
    dualMap e (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L)) =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (n : L') := by
  ext <;> simp [dualMap]

theorem base_comm {L L' : Type} [Field L] [Field L'] (e : L →+* L') :
    spMap (dualMap e) ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 (Sp L) =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
  simp only [Category.comp_id, Category.id_comp]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem push_eq {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (φ : G'.left ⟶ G.left) {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (i : splitTorus (Sp L) X ⟶ G) (i' : splitTorus (Sp L') X' ⟶ G') (κ : X ≃+ X')
    (hκ : ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') X')
      (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
        (t' ≫ i').left ≫ φ = (t ≫ i).left)
    (MT : LieModel (splitTorus (Sp L) X) (𝟙 _) (X →+ L)) (hMT : IsCocharLie MT)
    (MT' : LieModel (splitTorus (Sp L') X') (𝟙 _) (X' →+ L')) (hMT' : IsCocharLie MT') (δ : X →+ ℤ) :
    (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ i').left ≫ φ =
      spMap (dualMap e) ≫ (MT.pt ((Int.castAddHom L).comp δ) ≫ i).left := by
  set c := (Int.castAddHom L).comp δ with hc
  have hw : spMap (dualMap e) ≫ (MT.pt c).left ≫ (splitTorus (Sp L) X).hom =
      (Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e := by
    rw [Over.w (MT.pt c)]
    exact base_comm e
  let t : Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap L' (DualNumber L'))) ≫ 𝟙 (Sp L')) ≫ spMap e) ⟶
      splitTorus (Sp L) X := Over.homMk (spMap (dualMap e) ≫ (MT.pt c).left) (by simpa using hw)
  have h := hκ (DualNumber L') _ (MT'.pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom))) t (fun χ => by
    rw [charVal_comp (dualMap e) (MT.pt c) t rfl χ, hMT c χ, hMT' _ (κ χ)]
    simpa [hc] using dualMap_cast e (δ χ))
  rw [h]
  simp [t]

theorem cochars_baseChange : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  intro L L' _ _ e G G' _ _ φ τ τ' hP hTO V V' _ _ _ _ MV MV' j hj I hI
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  obtain ⟨κ, hκ⟩ := hTO
  obtain ⟨MT, hMT, hI⟩ := hI
  have hM' := isCocharLie_lieModel (X := τ'.X) (𝟙 (Sp L'))
  have hi := τ.i_hom
  have hp := fun δ => push_eq e φ τ.i τ'.i κ hκ MT hMT (lieModel (𝟙 (Sp L'))) hM' δ
  have hfw : ∀ (x : V) (δ : τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i →
      MV'.pt (j x) = (lieModel (𝟙 (Sp L'))).pt ((Int.castAddHom L').comp (δ.comp κ.symm.toAddMonoidHom)) ≫ τ'.i := by
    intro x δ hx
    refine pt_ext e hP _ _ ?_
    rw [hj x, hx, hp δ]
  refine ⟨lieModel (𝟙 (Sp L')), hM', fun x' => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨δ, hδ⟩ := (hI x).1 hx
    exact ⟨_, hfw x δ hδ⟩
  · rintro ⟨δ', hδ'⟩
    set δ : τ.X →+ ℤ := δ'.comp κ.toAddMonoidHom with hδ
    obtain ⟨x, hx⟩ := MV.onto _ (isTanAt_comp τ.i _ _ (MT.tan ((Int.castAddHom L).comp δ)))
    refine ⟨x, (hI x).2 ⟨δ, hx⟩, MV'.inj ?_⟩
    rw [hfw x δ hx, hδ', hδ]
    congr 3
    ext χ
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC
end
end

