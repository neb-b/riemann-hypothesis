module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHensCut
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Good.nbhd {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I) : Nbhd φ I := by
  refine ⟨h.etale, Ideal.quotientMap_injective' ?_, fun y => ?_⟩
  · obtain ⟨r, hr⟩ := h.retr
    have h1 : I.map φ ≤ RingHom.ker r := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change (r.comp φ) a = 0
      rw [hr]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    intro a ha
    have h2 : (r.comp φ) a = 0 := h1 ha
    rw [hr] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  · obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := h.surj s
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 ha).symm

theorem exists_obj (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) (A : Type) [CommRing A] (I : Ideal A) :
    ∃ (H : CommRingCat.{0}) (η : A →+* H), HenselianRing H (I.map η) ∧ IndNbhd η I ∧ Univ η I := by
  obtain ⟨Δ⟩ := h1 A I
  let c := colimit.cocone Δ.D
  have hc : IsColimit c := colimit.isColimit Δ.D
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  have hw : ∀ {j k : Δ.J} (e : j ⟶ k), (Δ.leg c j).comp (Δ.s j) = (Δ.leg c k).comp (Δ.s k) := fun {j k} e => by
    have h : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j := congrArg CommRingCat.Hom.hom (c.w e)
    rw [← Δ.nat e, ← RingHom.comp_assoc, h]
  have hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = (Δ.leg c j₀).comp (Δ.s j₀) := fun j =>
    (hw (IsFiltered.leftToMax j j₀)).trans (hw (IsFiltered.rightToMax j j₀)).symm
  refine ⟨c.pt, _, h2 A I Δ c hc _ hη, ?_, h3 A I Δ c hc _ hη⟩
  refine ⟨Δ.J, Δ.cat, Δ.filt, Δ.D, ⟨fun j => CommRingCat.ofHom (Δ.s j), fun j k e => ?_⟩, c.ι, ⟨hc⟩,
    fun j => ⟨(Δ.good j).nbhd, ?_⟩⟩
  · exact CommRingCat.hom_ext (Δ.nat e).symm
  · exact CommRingCat.hom_ext (hη j)

theorem goal_of (h1 : LeafDiag) (h2 : LeafColHens) (h3 : LeafColUniv) : LeafHens := by
  choose H η hh hi hu using exists_obj h1 h2 h3
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B), I ≤ J.comap φ →
      ∃! χ : H A I →+* H B J, χ.comp (η A I) = (η B J).comp φ := fun {A B} _ _ {I J} φ h =>
    hu A I _ _ (hh B J) _ fun a ha => Ideal.mem_map_of_mem (η B J) (h ha)
  refine ⟨⟨H, η, fun φ h => (key φ h).exists.choose, fun φ h => (key φ h).exists.choose_spec, fun A _ I h => ?_,
    fun φ ψ h h' h'' => ?_, hh, hi⟩⟩
  · exact (key _ h).unique (key _ h).exists.choose_spec rfl
  · refine (key _ h'').unique (key _ h'').exists.choose_spec ?_
    rw [RingHom.comp_assoc, (key φ h).exists.choose_spec, ← RingHom.comp_assoc, (key ψ h').exists.choose_spec,
      RingHom.comp_assoc]

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafIndExcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafNbhdExc : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  Nbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafHsCont : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem off_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (J : Ideal R) :
    off S (J.map ψ) = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ off R J := by
  ext x
  show ¬ ((Ideal.map ψ J : Set S) ⊆ (x : PrimeSpectrum S).asIdeal) ↔
    ¬ ((J : Set R) ⊆ (PrimeSpectrum.comap ψ x).asIdeal)
  simp only [SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
  exact Iff.rfl

theorem dbl.inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl.map_comp' {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) :
    dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  set_option synthInstance.maxHeartbeats 200000 in
  apply pushout.hom_ext
  · change dbl.inl P'' ≫ dbl.map (φ ≫ ψ) = dbl.inl P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inl_map', ← Category.assoc, dbl.inl_map', Category.assoc, dbl.inl_map', Arrow.comp_right,
      Category.assoc]
  · change dbl.inr P'' ≫ dbl.map (φ ≫ ψ) = dbl.inr P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right,
      Category.assoc]

theorem Hs.pull_comp' (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (φ ≫ ψ)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map φ) _ n (GlobalTheory.EtC.pull _ (dbl.map ψ) _ n x.1)
  rw [dbl.map_comp', pull_comp]

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap (f ≫ g) U'' U h = opnMap f U'' U' h1 ≫ opnMap g U' U h2 := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [Functor.map_comp]

theorem opnMap_congr {X' X : Scheme.{0}} {f g : X' ⟶ X} (e : f = g) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U)
    (h' : U' ≤ g ⁻¹ᵁ U) : opnMap f U' U h = opnMap g U' U h' := by
  subst e; rfl

theorem leafIndExc_of (hN : LeafNbhdExc) (hC : LeafHsCont) : LeafIndExc := by
  intro a1 a4 b1 q A B _ _ φ I hI hInd hq h n i
  obtain ⟨J, _, _, D, s, t, ⟨hcol⟩, hst⟩ := hInd
  have hs : ∀ j, Nbhd (A := A) (s.app j).hom I := fun j => (hst j).1
  have he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ := fun j => (hst j).2
  obtain ⟨hsurj, hinj⟩ := hC a1 a4 b1 q φ I hI hq J D s t hcol he n i
  have hsle : ∀ j, off (D.obj j) (I.map (s.app j).hom) ≤ Spec.map (s.app j) ⁻¹ᵁ off A I := fun j =>
    le_of_eq (off_map (s.app j).hom I)
  have hE : ∀ j, Function.Bijective (Hs.pull q (opnMap (Spec.map (s.app j)) _ _ (hsle j)) n i) := fun j =>
    hN a1 q (s.app j).hom I (hs j) hq (hsle j) n i
  have hB : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := fun j => by
    intro x hx
    have hx' := h hx
    rw [← he j, Spec.map_comp] at hx'
    have e := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e
    rw [e]
    exact hx'
  have hfac : ∀ j (h1 : off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom)),
      opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h =
        opnMap (Spec.map (t.app j)) _ _ h1 ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
    intro j h1
    have hcomp : off B (I.map φ) ≤ (Spec.map (t.app j) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
      rw [← Spec.map_comp, he j]; exact h
    exact (opnMap_congr (by rw [← Spec.map_comp, he j]) _ _ _ hcomp).trans
      (opnMap_comp _ _ _ _ _ h1 (hsle j) hcomp)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    rw [hfac j (hB j), Hs.pull_comp'] at hz
    obtain ⟨k, f, h', hk⟩ := hinj j (hB j) _ hz
    have hn : s.app k = s.app j ≫ D.map f := by
      have := s.naturality f
      simpa using this
    have hk' : opnMap (Spec.map (s.app k)) _ _ (hsle k) =
        opnMap (Spec.map (D.map f)) _ _ h' ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
      have hcomp : off (D.obj k) (I.map (s.app k).hom) ≤ (Spec.map (D.map f) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
        rw [← Spec.map_comp, ← hn]; exact hsle k
      exact (opnMap_congr (by rw [← Spec.map_comp, ← hn]) _ _ _ hcomp).trans
        (opnMap_comp _ _ _ _ _ h' (hsle j) hcomp)
    apply (injective_iff_map_eq_zero _).1 (hE k).1
    rw [hk', Hs.pull_comp', hk]
  · intro x
    obtain ⟨j, h1, y, hy⟩ := hsurj x
    obtain ⟨z, hz⟩ := (hE j).2 y
    exact ⟨z, by rw [hfac j h1, Hs.pull_comp', hz, hy]⟩

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSemiPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem LeafSemi_of : LeafSemi := by
  intro hA9 hG
  intro q _ X Z S p ι _ d e _ _ hq U hU N i
  obtain ⟨gys, rs, hgys⟩ := hG d
  let P : SP d := ⟨X, Z, S, p, ι, e, U, inferInstance, inferInstance, inferInstance, hU⟩
  have hqX : IsUnit (q : Γ(P.X, ⊤)) := by
    simpa using hq.map p.appTop.hom
  have hex := (hgys q P hqX).1
  have hsub : ∀ m j : ℤ, m < 0 → Subsingleton (Ht q (sch.obj Z) m j) :=
    fun m j hm => (hA9 (ZMod q) (tw q j)).1 _ m hm
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
      rw [Subsingleton.elim b 0, map_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d - 1 := ⟨N - 2 * d + 1, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      intro u
      exact ((hex m j).1 u).1 (Subsingleton.elim _ _)
  · intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
    have hm : m < 0 := by omega
    have := hsub m j hm
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
    rw [Subsingleton.elim b 0, map_zero]

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Hoc
variable {J : Type} [SmallCategory J]

def hocF (J : Type) [SmallCategory J] : (J ⥤ PSh) ⥤ Spc :=
  flipFunctor _ _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (Functor.elementsFunctor ⋙ nerveFunctor) ⋙ flipFunctor _ _ _

abbrev hoc (D : J ⥤ PSh) : Spc := (hocF J).obj D

def chn {D : J ⥤ PSh} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ} (x : ((hoc D).obj n).obj U) :
    Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements := x

def Coc (D : J ⥤ PSh) {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) : Prop := ∀ j k (f : j ⟶ k), D.map f ≫ c k = c j

def aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) : hoc D ⟶ disc.obj Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (c ((chn x).obj 0).1).app U ((chn x).obj 0).2
      naturality := fun U U' f => by
        ext x
        exact ConcreteCategory.congr_hom ((c ((chn x).obj 0).1).naturality f) ((chn x).obj 0).2 }
  naturality n m θ := by
    ext U x
    have g := (chn x).map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ g.1) U) ((chn x).obj 0).2
    refine Eq.trans ?_ h
    exact congrArg (fun y => (c ((chn x).obj (θ.unop.toOrderHom 0)).1).app U y) g.2.symm

theorem map_aug {D' D : J ⥤ PSh} {Y : PSh} (α : D' ⟶ D) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c')
    (hc : Coc D c) (h : ∀ j, α.app j ≫ c j = c' j) : (hocF J).map α ≫ aug c hc = aug c' hc' := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).1) U) ((chn x).obj 0).2

def mkChn {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) (s : ∀ i, F.obj (σ.obj i))
    (h : ∀ i k (g : i ⟶ k), F.map (σ.map g) (s i) = s k) : I ⥤ F.Elements where
  obj i := F.elementsMk (σ.obj i) (s i)
  map g := Functor.Elements.homMk (σ.map g) (h _ _ g)
  map_id i := Functor.Elements.hom_ext (σ.map_id i)
  map_comp g g' := Functor.Elements.hom_ext (σ.map_comp g g')

theorem mkChn_congr {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) {s s' : ∀ i, F.obj (σ.obj i)} (e : s = s') h h' :
    mkChn σ s h = mkChn σ s' h' := by subst e; rfl

theorem laurent_adjoin_eq_of_image_eq (D : J ⥤ PSh) {n : ℕ} (σ : Fin (n + 1) ⥤ J) (i k : Fin (n + 1)) (g : i ⟶ k) :
    D.map (σ.map (homOfLE (Fin.zero_le i))) ≫ D.map (σ.map g) = D.map (σ.map (homOfLE (Fin.zero_le k))) := by
  rw [← D.map_comp, ← σ.map_comp]; rfl

def inj (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : D.obj (σ.obj 0) ⟶ (hoc D).obj n where
  app U := TypeCat.ofHom fun x => mkChn (F := D.flip.obj U) σ (fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
    fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x
  naturality U U' f := by
    ext x
    exact mkChn_congr (F := D.flip.obj U') σ
      (funext fun i => ConcreteCategory.congr_hom ((D.map (σ.map (homOfLE (Fin.zero_le i)))).naturality f) x)
      (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U') _)
      (fun i k g => by
        have a := ConcreteCategory.congr_hom ((D.map (σ.map g)).naturality f) ((D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
        exact a.trans (congrArg ((D.obj (σ.obj k)).map f)
          (ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x)))

end Hoc

def pbRel {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pullback π' g ⟶ pullback π g := pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

def abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abv U π' ⟶ abv U π :=
  Arrow.homMk (pbRel (sch.map U.ι) a π' π h) a (pullback.lift_fst _ _ _)

def Prd (q : ℕ) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {m j : ℤ} (c : Hs q (opn U) m j) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : Ht q E n i => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)

def Loc {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g : Y ⟶ X), QuasiIso ((chains R).map (pullback.snd π (sch.map g)))

def lev (n : SimplexCategoryᵒᵖ) : Arrow Spc ⥤ Arrow Spc := ((evaluation _ _).obj n ⋙ disc).mapArrow

def LeafLevel : Prop := ∀ (J : Type) [SmallCategory J] (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ),
  Nonempty (IsColimit (Cofan.mk ((hoc D).obj n) (inj D n)))

def LeafSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ n : ℤ, Function.Bijective fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x

def LeafRel : Prop := ∀ (q : ℕ) (i : ℤ),
  ∃ e : ∀ (P : Arrow Spc) (n : ℤ), HK _ (cokernel ((chains (ZMod q)).map P.hom)) (tw q i) n ≃+ Hs q P n i,
    (∀ (P : Arrow Spc) (n : ℤ) (p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom)),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ → (chains _).map (dbl.inr P) ≫ p = 0 →
      ∀ x, (e P n x).1 = HK.pull _ p (tw q i) n x)

def LeafExcLevel : Prop := A3 → ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ n, Exc q ((lev n).map φ)) → Exc q φ

def LeafPrdLevel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X) (m j : ℤ)
  (c : Hs q (opn U) m j), (∀ n, Prd q U (E := disc.obj (E.obj n)) (disc.map (π.app n)) c) → Prd q U π c

def LeafActNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P' P : Arrow Spc) (φ : P' ⟶ P) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b)

def LeafHsSum : Prop := ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)) (n i : ℤ),
  Function.Bijective fun (x : Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i) (a : A) =>
    Hs.pull q (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) n i x

def LeafFstHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D : J ⥤ PSh) (Y G : PSh)
  (g : G ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c), (∀ j, Eqv R (pullback.fst (disc.map (c j)) (disc.map g)) F) →
  Eqv R (pullback.fst (aug c hc) (disc.map g)) F

def LeafRelHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Eqv R (pbRel (disc.map g) (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)) F) →
  Eqv R (pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h') F

def LeafExcHoc : Prop := A3 → ∀ (q : ℕ) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D) (X : Scheme.{0})
  (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j))) →
  Exc q (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h')

def LeafPrdHoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] (D : J ⥤ PSh) (X : Scheme.{0}) (U : X.Opens)
  (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc : Coc D c) (m k : ℤ) (b : Hs q (opn U) m k),
  (∀ j, Prd q U (E := disc.obj (D.obj j)) (disc.map (c j)) b) → Prd q U (aug c hc) b

def LeafLoc : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j), Loc (aug _ hc)

def LeafLocExc : Prop := A1 → ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X), Loc π → Exc q (abvMap U π)

def LeafPush : Prop := ∀ (J' J : Type) [SmallCategory J'] [SmallCategory J] (D' : J' ⥤ PSh) (D : J ⥤ PSh) (G : J' ⥤ J)
  (α : D' ⟶ G ⋙ D) (Y' Y : PSh) (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c),
  (∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) → ∃ b : hoc D' ⟶ hoc D, b ≫ aug c hc = aug c' hc' ≫ disc.map f

end LateralTheory.CohomologicalPurity.TubeCut
end
end

