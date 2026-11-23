module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem Model.isPullback_j (M : Model R A) :
    IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · have : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, M.e.hom_inv_id]; rfl
    simp [Model.j, reassoc_of% this]
  · have := Over.w M.e.hom
    simpa using this.symm

theorem Model.quasiCompact_j (M : Model R A) : QuasiCompact M.j :=
  MorphismProperty.of_isPullback M.isPullback_j.flip inferInstance

variable [IsDomain R] [IsFractionRing R K]

theorem Model.dominant_j (M : Model R A) : IsSchemeTheoreticallyDominant M.j := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  exact IsSchemeTheoreticallyDominant.of_isPullback M.isPullback_j.flip

theorem Model.hom_ext_of_flat (M : Model R A) {P X : Scheme.{0}} (p : P ⟶ M.Y.left) [Flat p]
    (s : X ⟶ Sp R) [IsSeparated s] {a b : P ⟶ X} (hab : a ≫ s = b ≫ s)
    (h : pullback.fst p M.j ≫ a = pullback.fst p M.j ≫ b) : a = b := by
  have := M.dominant_j
  have := M.quasiCompact_j
  have : IsSchemeTheoreticallyDominant (pullback.fst p M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p M.j).flip
  have : IsSeparated (Over.mk s).hom := ‹_›
  have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (a ≫ s)) (X := Over.mk s)
    (pullback.fst p M.j) (a := Over.homMk a rfl) (b := Over.homMk b hab.symm) h
  exact congr(($this).left)


omit [IsDomain R] [IsFractionRing R K] in
theorem Extends.comp_eq {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {W : Scheme.{0}} (u : W ⟶ U.toScheme)
    (v : W ⟶ A.left) (e : u ≫ U.ι = v ≫ M.j) : u ≫ g = v ≫ f.left ≫ N.j := by
  have P := isPullback_morphismRestrict M.j U
  rw [← P.lift_fst u v e, Category.assoc, h.2, P.lift_snd_assoc]

theorem exists_glue (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left → M.Y.left.Opens)
    (g : ∀ y, (U y).toScheme ⟶ N.Y.left) (hU : ∀ y, y ∈ U y) (hg : ∀ y, Extends M N f (U y) (g y)) :
    ∃ G : M.Y ⟶ N.Y, M.j ≫ G.left = f.left ≫ N.j ∧ ∀ y, (U y).ι ≫ G.left = g y := by
  have := N.sep
  have hc : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hc
  have hgl : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine M.hom_ext_of_flat (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) N.Y.hom ?_ ?_
    · rw [Category.assoc, Category.assoc, (hg x).1, (hg y).1, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc,
        (hg x).comp_eq _ (pullback.snd _ M.j) (by rw [Category.assoc]; exact pullback.condition),
        (hg y).comp_eq _ (pullback.snd _ M.j)
          (by rw [Category.assoc, ← pullback.condition (f := (U x).ι)]; exact pullback.condition)]
  obtain ⟨G, hG⟩ : ∃ G : M.Y.left ⟶ N.Y.left, ∀ y, (U y).ι ≫ G = g y :=
    ⟨𝒰.glueMorphisms g hgl, fun y => 𝒰.ι_glueMorphisms g hgl y⟩
  refine ⟨Over.homMk G (𝒰.hom_ext _ _ fun y : M.Y.left => ?_), ?_, hG⟩
  · change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    rw [← Category.assoc, hG, (hg y).1]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ M.j) _ _ fun y : M.Y.left => ?_
    change pullback.fst M.j (U y).ι ≫ M.j ≫ G = pullback.fst M.j (U y).ι ≫ f.left ≫ N.j
    rw [pullback.condition_assoc, hG]
    exact (hg y).comp_eq _ _ pullback.condition.symm

theorem ext_unique (M : Model R A) (N : Model R A') {a b : M.Y ⟶ N.Y}
    (h : M.j ≫ a.left = M.j ≫ b.left) : a = b := by
  have := M.dominant_j
  have := N.sep
  exact over_ext_of_schemeTheoreticallyDominant M.j h

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma isPullback_model_j_spMap_algebraMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma eq_of_openImmersion_of_eq_on_genericFibre [IsDomain R] [IsFractionRing R K]
    (M : _root_.GlobalTheory.SS.Model R A)
    (N : _root_.GlobalTheory.SS.Model R A') {W : Scheme} (i : W ⟶ M.Y.left)
    [IsOpenImmersion i] (a b : W ⟶ N.Y.left)
    (ha : a ≫ N.Y.hom = i ≫ M.Y.hom)
    (hb : b ≫ N.Y.hom = i ≫ M.Y.hom)
    (h : pullback.snd M.j i ≫ a = pullback.snd M.j i ≫ b) :
    a = b := by
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have hP := ((IsPullback.of_hasPullback M.j i).flip.paste_vert
    (isPullback_model_j_spMap_algebraMap M)).flip
  haveI := IsSchemeTheoreticallyDominant.of_isPullback hP
  have := _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (i ≫ M.Y.hom))
    (X := N.Y) (pullback.snd M.j i)
    (a := Over.homMk a ha) (b := Over.homMk b hb) h
  exact congrArg (fun c => c.left) this

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma comp_eq_of_extends_of_genericFibre_comm {M : _root_.GlobalTheory.SS.Model R A}
    {N : _root_.GlobalTheory.SS.Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : (U : Scheme) ⟶ N.Y.left} (hg : _root_.GlobalTheory.SS.Extends M N f U g)
    {T : Scheme} (t : T ⟶ U) (s : T ⟶ A.left) (hts : s ≫ M.j = t ≫ U.ι) :
    t ≫ g = s ≫ f.left ≫ N.j := by
  have hP := isPullback_morphismRestrict M.j U
  have h2 := hg.2
  rw [← hP.lift_fst t s hts.symm, Category.assoc, h2, ← Category.assoc, hP.lift_snd]


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
theorem _root_.GlobalTheory.SS.existsUnique_extension_of_forall_defAt :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M : _root_.GlobalTheory.SS.Model R A)
      (N : _root_.GlobalTheory.SS.Model R A') (f : A ⟶ A'),
      (∀ y, _root_.GlobalTheory.SS.DefAt M N f y) →
        ∃! g : M.Y ⟶ N.Y,
          M.j ≫ g.left = f.left ≫ N.j := by
  intro R K _ _ _ _ _ _ A A' M N f hdef
  choose U g hyU hg using hdef
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  have key : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine eq_of_openImmersion_of_eq_on_genericFibre M N (pullback.fst (U x).ι (U y).ι ≫ (U x).ι)
      _ _ ?_ ?_ ?_
    · simp only [Category.assoc, (hg x).1]
    · simp only [Category.assoc, (hg y).1]
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    · have e1 := comp_eq_of_extends_of_genericFibre_comm (hg x)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.fst _ _)
        (pullback.fst _ _) (by rw [Category.assoc]; exact pullback.condition)
      have e2 := comp_eq_of_extends_of_genericFibre_comm (hg y)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.snd _ _)
        (pullback.fst _ _) (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition)
      simp only [Category.assoc] at e1 e2
      rw [e1, e2]
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hcov
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ g y :=
    fun x y => key x y
  let G := 𝒰.glueMorphisms g hcompat
  have hG : ∀ y, (U y).ι ≫ G = g y := fun y => 𝒰.ι_glueMorphisms g hcompat y
  have hw : G ≫ N.Y.hom = M.Y.hom := by
    refine 𝒰.hom_ext _ _ fun y => ?_
    change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    exact (Category.assoc _ _ _).symm.trans ((hG y =≫ _).trans (hg y).1)
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI := IsSchemeTheoreticallyDominant.of_isPullback (isPullback_model_j_spMap_algebraMap M).flip
  have hex : M.j ≫ G = f.left ≫ N.j := by
    have hcovA : TopologicalSpace.IsOpenCover (fun y => M.j ⁻¹ᵁ U y) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro a _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨M.j a, hyU _⟩
    refine (A.left.openCoverOfIsOpenCover _ hcovA).hom_ext _ _ fun y => ?_
    change (M.j ⁻¹ᵁ U y).ι ≫ M.j ≫ G =
      (M.j ⁻¹ᵁ U y).ι ≫ f.left ≫ N.j
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact (M.j ∣_ U y ≫= hG y).trans (hg y).2
  exact ⟨Over.homMk G hw, hex, fun g' hg' =>
    _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant M.j (hg'.trans hex.symm)⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGPowAndClosedSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.FrobSub

def Raises {X : Scheme.{0}} (φ : X ⟶ X) (n : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

theorem Raises.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {a b : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (h₁ : Raises φ a U f) (h₂ : Raises ψ b U f) : Raises (φ ≫ ψ) (a * b) U f := by
  obtain ⟨e₁, p₁⟩ := h₁
  obtain ⟨e₂, p₂⟩ := h₂
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e₂, ← e₁], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e₂.le e₁.le, CommRingCat.hom_comp, RingHom.comp_apply, p₂,
    map_pow, p₁, ← pow_mul]

theorem Raises.mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) {U : G.left.Opens} {f : Γ(G.left, U)}
    (h : Raises (F ^ m).asHom.left (q ^ m) U f) (n : ℕ) (hn : 1 ≤ n) :
    Raises (F ^ (m * n)).asHom.left (q ^ (m * n)) U f := by
  induction n, hn using Nat.le_induction with
  | base => rwa [Nat.mul_one]
  | succ n hn ih =>
    have := h.comp ih
    rw [Nat.mul_succ, pow_add, End.mul_asHom, pow_add, mul_comm (q ^ (m * n))]
    exact this

theorem Raises.pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {φ : X ⟶ X} {ψ : Y ⟶ Y} (hc : ψ ≫ ν = ν ≫ φ) {a : ℕ}
    {V : X.Opens} {g : Γ(X, V)} (h : Raises φ a V g) : Raises ψ a (ν ⁻¹ᵁ V) ((ν.app V).hom g) := by
  obtain ⟨e, p⟩ := h
  have e' : ν ⁻¹ᵁ V = ψ ⁻¹ᵁ ν ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, ← e]
  refine ⟨e', ?_⟩
  have k : ∀ (θ θ' : Y ⟶ X) (_ : θ = θ') h h', θ.appLE V (ν ⁻¹ᵁ V) h = θ'.appLE V (ν ⁻¹ᵁ V) h' := by
    rintro _ _ rfl _ _; rfl
  have k2 : ν.appLE V (ν ⁻¹ᵁ V) le_rfl ≫ ψ.appLE _ _ e'.le =
      φ.appLE V V e.le ≫ ν.appLE V (ν ⁻¹ᵁ V) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact k _ _ hc _ _
  rw [Scheme.Hom.app_eq_appLE]
  have := congrArg (fun t => t.hom g) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, p, map_pow]

theorem Raises.of_cover {X : Scheme.{0}} {φ : X ⟶ X} {a : ℕ} {U : X.Opens} {f : Γ(X, U)} {I : Type}
    (V : I → X.Opens) (hV : ∀ i, V i ≤ U) (hU : U ≤ iSup V)
    (h : ∀ i, Raises φ a (V i) ((X.presheaf.map (homOfLE (hV i)).op).hom f)) : Raises φ a U f := by
  have hU' : U = iSup V := le_antisymm hU (iSup_le hV)
  have e : U = φ ⁻¹ᵁ U := by
    rw [hU', Scheme.Hom.preimage_iSup]
    exact iSup_congr fun i => (h i).1
  refine ⟨e, ?_⟩
  refine X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hU _ _ fun i => ?_
  obtain ⟨e', p⟩ := h i
  have k2 : φ.appLE U U e.le ≫ X.presheaf.map (homOfLE (hV i)).op =
      X.presheaf.map (homOfLE (hV i)).op ≫ φ.appLE _ _ e'.le := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have := congrArg (fun t => t.hom f) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans (p.trans (map_pow _ _ _).symm)

theorem pow_comm_hom {C : Type*} [Category C] {N G : C} (ν : N ⟶ G) (F : End G) (F' : End N)
    (h : F'.asHom ≫ ν = ν ≫ F.asHom) (m : ℕ) :
    (F' ^ m).asHom ≫ ν = ν ≫ (F ^ m).asHom := by
  induction m with
  | zero => simp [End.one_asHom]
  | succ m ih =>
    simp only [pow_succ, End.mul_asHom, Category.assoc] at *
    rw [ih, reassoc_of% h]

theorem isMonHom_pow {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G)
    (h : IsMonHom F.asHom) (m : ℕ) : IsMonHom (F ^ m).asHom := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 G))
  | succ m ih =>
    rw [pow_succ, End.mul_asHom]
    infer_instance

end GlobalTheory.SS.FrobSub


open GlobalTheory.SS.FrobSub in
theorem GlobalTheory.SS.frobG_pow_and_closed_subgroup :
    ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G →
      ∀ (F : End G) (q : ℕ), FrobG G F q →
        (∀ m, 1 ≤ m → FrobG G (F ^ m) (q ^ m)) ∧
        ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (F' : End N),
          IsMonHom ν → IsClosedImmersion ν.left → IsMonHom F'.asHom →
          F'.asHom ≫ ν = ν ≫ F.asHom → FrobG N F' q := by
  intro k _ G _ _ F q hF
  refine ⟨fun m hm => ⟨isMonHom_pow G F hF.1 m, fun U hU f => ?_⟩, fun N _ ν F' _ hν hF' hc => ⟨hF', fun U hU f => ?_⟩⟩
  · obtain ⟨n, hn, h⟩ := hF.2 U hU f
    refine ⟨n, hn, ?_⟩
    have := Raises.mul F q n h m hm
    rw [mul_comm, pow_mul, pow_mul] at this
    exact this
  · have key : ∀ x : U, ∃ (W : N.left.Opens) (hW : W ≤ U) (m : ℕ), x.1 ∈ W ∧ 1 ≤ m ∧
        Raises (F' ^ m).asHom.left (q ^ m) W ((N.left.presheaf.map (homOfLE hW).op).hom f) := by
      intro x
      obtain ⟨W, hW, hWU⟩ := ν.left.isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
      have hx : ν.left x.1 ∈ (⟨W, hW⟩ : G.left.Opens) := by
        show x.1 ∈ ν.left ⁻¹' W
        rw [hWU]; exact x.2
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
      have hle : ν.left ⁻¹ᵁ V ≤ U := fun y hy => by
        have : y ∈ ν.left ⁻¹' W := hVW hy
        rwa [hWU] at this
      obtain ⟨g, hg⟩ := ν.left.app_surjective V hV ((N.left.presheaf.map (homOfLE hle).op).hom f)
      obtain ⟨m, hm, h⟩ := hF.2 V hV g
      refine ⟨_, hle, m, hxV, hm, ?_⟩
      rw [← hg]
      refine Raises.pull ν.left ?_ h
      exact congrArg (fun t => t.left) (pow_comm_hom ν F F' hc m)
    choose W hW m hxW hm hR using key
    obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun x => (W x : Set N.left)) (fun x => (W x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)
    have hpos : 1 ≤ ∏ x ∈ t, m x := Finset.one_le_prod fun x _ => hm x
    refine ⟨∏ x ∈ t, m x, hpos, ?_⟩
    refine Raises.of_cover (fun x : t => W x.1) (fun x => hW x.1) (fun y hy => ?_) fun x => ?_
    · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy'⟩
    · obtain ⟨n, hn⟩ := Finset.dvd_prod_of_mem m x.2
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by rw [hn, h0] at hpos; simp at hpos
      rw [hn]
      exact Raises.mul F' q _ (hR x.1) n hn1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGSplitTorusPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem appTop_pow_mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) (f : Γ(G.left, ⊤))
    (h : (F ^ m).asHom.left.appTop.hom f = f ^ (q ^ m)) (j : ℕ) :
    (F ^ (m * j)).asHom.left.appTop.hom f = f ^ (q ^ (m * j)) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, pow_one]
    change (Scheme.Hom.appTop (𝟙 G.left)).hom f = f
    simp
  | succ j ih =>
    have e : (F ^ (m * (j + 1))).asHom.left =
        (F ^ m).asHom.left ≫ (F ^ (m * j)).asHom.left := by
      rw [Nat.mul_succ, pow_add]; rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h,
      ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]

theorem isAffine_splitTorus (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Sp k) X).left := by
  have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Spec ZU.{0}) := inferInstance
  exact inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))

theorem frobG_splitTorus_pow :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q →
        ∃ m, 1 ≤ m ∧ ∀ l, (F ^ (m * l)).asHom = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by
  intro k _ X _ _ _ F q hF
  classical
  have := isAffine_splitTorus k X
  have key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧
      (F ^ m).asHom.left.appTop.hom
        (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m) := by
    intro χ
    obtain ⟨m, hm, h, hh⟩ := hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val
    refine ⟨m, hm, ?_⟩
    rw [← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  choose n0 hn1 hn using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩
  let e := splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)
  apply e.injective
  rw [map_pow]
  have hgen : ∀ χ ∈ s, e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom (Multiplicative.ofAdd χ) =
      (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ) := by
    intro χ hχ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n0 hχ
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val,
      splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]
    congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x.toAdd ∈ Submodule.span ℤ (s : Set X) := by rw [hs]; trivial
  generalize e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom = a at hgen ⊢
  generalize (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢
  change a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)
  generalize x.toAdd = w at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]
  | smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]

end GlobalTheory.SS
end

