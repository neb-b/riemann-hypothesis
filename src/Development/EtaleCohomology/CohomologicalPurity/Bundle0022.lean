module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0015
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0014

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocBasePf
section
set_option linter.unusedSimpArgs false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

theorem isPullback_of_app {K C : Type*} [Category K] [Category C] [HasPullbacks C] {P X Y Z : K ⥤ C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd w)
    (evaluationJointlyReflectsLimits _ fun k =>
      (isLimitMapConePullbackConeEquiv ((evaluation K C).obj k) w).symm (h k).isLimit)

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)

include hc in
theorem cw {j k : J} (f : j ⟶ k) : D.map f ≫ c k = c j :=
  yoneda.map_injective (by simpa using hc j k f)

def D' : J ⥤ Scheme.{0} where
  obj j := pullback (c j) g
  map {j k} f := pullback.map (c j) g (c k) g (D.map f) (𝟙 Y) (𝟙 X) (by simp [cw D c hc f]) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]
    exact (congrArg (pullback.fst (c j) g ≫ ·) (D.map_id j)).trans (Category.comp_id _)
  map_comp f f' := by apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]

def c' (j : J) : (D' D c hc g).obj j ⟶ Y := pullback.snd (c j) g

theorem hc' : Coc (D' D c hc g ⋙ yoneda) fun j => yoneda.map (c' D c hc g j) := by
  intro j k f
  rw [Functor.comp_map, ← yoneda.map_comp]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def α : D' D c hc g ⋙ yoneda ⟶ D ⋙ yoneda where
  app j := yoneda.map (pullback.fst (c j) g)
  naturality j k f := by
    have e : (D' D c hc g).map f ≫ pullback.fst (c k) g = pullback.fst (c j) g ≫ D.map f := pullback.lift_fst _ _ _
    exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map e).trans (yoneda.map_comp _ _))

theorem sq : (hocF J).map (α D c hc g) ≫ aug _ hc = aug _ (hc' D c hc g) ≫ sch.map g := by
  ext n U x
  have key : ∀ j (a : unop U ⟶ pullback (c j) g), (a ≫ pullback.fst (c j) g) ≫ c j = (a ≫ pullback.snd (c j) g) ≫ g :=
    fun j a => by rw [Category.assoc, Category.assoc, pullback.condition]
  exact key _ _

theorem snd_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ (D' D c hc g).obj j) :
    (a ≫ (D' D c hc g).map f) ≫ c' D c hc g k = a ≫ c' D c hc g j := by
  rw [Category.assoc]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem snd_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D' D c hc g ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c' D c hc g (z.obj i).1 = (z.obj 0).2 ≫ c' D c hc g (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  exact snd_map D c hc g _ _

include hc in
theorem c_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c (z.obj i).1 = (z.obj 0).2 ≫ c (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  change ((z.obj 0).2 ≫ D.map _) ≫ _ = _
  rw [Category.assoc, cw D c hc]

theorem pt_ext {U : Scheme.{0}ᵒᵖ} (p q : Σ j, unop U ⟶ pullback (c j) g)
    (h1 : (⟨p.1, p.2 ≫ pullback.fst (c p.1) g⟩ : Σ j, unop U ⟶ D.obj j) = ⟨q.1, q.2 ≫ pullback.fst (c q.1) g⟩)
    (h2 : p.2 ≫ pullback.snd (c p.1) g = q.2 ≫ pullback.snd (c q.1) g) : p = q := by
  obtain ⟨j, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨rfl, h⟩ := h1
  have h' := eq_of_heq h
  congr 1
  exact pullback.hom_ext h' h2

include hc in
theorem lift_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ D.obj j) (b : V ⟶ D.obj k) (y : V ⟶ Y)
    (ha : a ≫ c j = y ≫ g) (hb : b ≫ c k = y ≫ g) (hab : a ≫ D.map f = b) :
    (pullback.lift a y ha : V ⟶ (D' D c hc g).obj j) ≫ (D' D c hc g).map f = pullback.lift b y hb := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id, D', hab]

theorem pb : IsPullback ((hocF J).map (α D c hc g)) (aug _ (hc' D c hc g)) (aug _ hc) (sch.map g) := by
  refine isPullback_of_app (sq D c hc g) fun n => isPullback_of_app ?_ fun U => ?_
  · exact NatTrans.congr_app (sq D c hc g) n
  have elem_ext {F : J ⥤ Type} (a b : F.Elements)
      (h : (⟨a.obj, a.val⟩ : Σ j, F.obj j) = ⟨b.obj, b.val⟩) : a = b := by
    cases a
    cases b
    cases h
    rfl
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app (sq D c hc g) n) U
  · rintro x y ⟨h1, h2⟩
    change chn x = chn y
    refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
    intro i
    have he : (⟨((chn x).obj i).obj, ((chn x).obj i).val⟩ : Σ j, unop U ⟶ pullback (c j) g) =
        ⟨((chn y).obj i).obj, ((chn y).obj i).val⟩ := by
      refine pt_ext D c g _ _ ?_ ?_
      · have hh := congrArg (fun z => (chn z).obj i) h1
        exact congrArg (fun z => (⟨z.obj, z.val⟩ : Σ j, unop U ⟶ D.obj j)) hh
      · exact (snd_chain D c hc g (chn x) i).trans (h2.trans (snd_chain D c hc g (chn y) i).symm)
    exact elem_ext _ _ he
  · intro x₂ x₃ h
    have e : ∀ i, ((chn x₂).obj i).2 ≫ c ((chn x₂).obj i).1 = x₃ ≫ g := fun i =>
      (c_chain D c hc (chn x₂) i).trans h
    refine ⟨mkChn (F := (D' D c hc g ⋙ yoneda).flip.obj U) (chn x₂ ⋙ CategoryOfElements.π _)
      (fun i => pullback.lift ((chn x₂).obj i).2 x₃ (e i)) (fun i k f => ?_), ?_, ?_⟩
    · exact lift_map D c hc g _ _ _ x₃ _ _ ((chn x₂).map f).2
    · change chn _ = chn x₂
      refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
      intro i
      apply elem_ext
      refine Sigma.ext rfl (heq_of_eq ?_)
      change pullback.lift _ _ _ ≫ pullback.fst (c ((chn x₂).obj i).1) g = _
      exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x₃
      exact pullback.lift_snd _ _ _

end

theorem hr {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (ho : ∀ j, IsOpenImmersion (c j)) (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)
    (j : J) (y : Y) : y ∈ Set.range (c' D c hc g j) ↔ g y ∈ Set.range (c j) := by
  have := ho j
  change y ∈ Set.range (pullback.snd (c j) g) ↔ _
  rw [IsOpenImmersion.range_pullbackSnd]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

namespace LateralTheory.CohomologicalPurity.TubeCut
open LocBasePf

theorem LeafLocBase_of : EtaleLocBase := by
  intro J _ D X c ho hcov hdir hc Y g
  refine ⟨D' D c hc g, c' D c hc g, ?_, ?_, ?_, hc' D c hc g, ⟨?_⟩⟩
  · intro j
    have := ho j
    change IsOpenImmersion (pullback.snd (c j) g)
    infer_instance
  · intro y
    obtain ⟨j, hj⟩ := hcov (g y)
    exact ⟨j, (hr D c ho hc g j y).2 hj⟩
  · intro y j k h1 h2
    obtain ⟨l, hl1, hl2, hl⟩ := hdir (g y) j k ((hr D c ho hc g j y).1 h1) ((hr D c ho hc g k y).1 h2)
    exact ⟨l, hl1, hl2, (hr D c ho hc g l y).2 hl⟩
  · exact Arrow.isoMk (pb D c hc g).isoPullback.symm (Iso.refl _)
      ((IsPullback.isoPullback_inv_snd _).trans (Category.comp_id _).symm)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

abbrev evNU (n : ℕ) (U : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op U)

theorem pb_ext {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (x y : Sx (pullback f g) n U)
    (h1 : ((pullback.fst f g).app _).app _ x = ((pullback.fst f g).app _).app _ y)
    (h2 : ((pullback.snd f g).app _).app _ x = ((pullback.snd f g).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesPullback.iso G f g ≪≫ Types.pullbackIsoPullback (G.map f) (G.map g)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  apply Subtype.ext
  have a1 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_fst G f g))
  have a2 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_snd G f g))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
    exact (a1 x).trans (h1.trans (a1 y).symm)
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    exact (a2 x).trans (h2.trans (a2 y).symm)

theorem pb_mk {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (a : Sx X n U) (b : Sx Y n U)
    (h : (f.app _).app _ a = (g.app _).app _ b) : ∃ x : Sx (pullback f g) n U,
    ((pullback.fst f g).app _).app _ x = a ∧ ((pullback.snd f g).app _).app _ x = b := by
  let G := evNU n U
  let z : Types.PullbackObj (G.map f) (G.map g) := ⟨(a, b), h⟩
  refine ⟨(PreservesPullback.iso G f g).inv ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z), ?_, ?_⟩
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_fst G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (G.map f) (G.map g))) z
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_snd G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd (G.map f) (G.map g))) z

theorem pr_ext {X Y : Spc} {n : ℕ} {U : Scheme.{0}} (x y : Sx (X ⨯ Y) n U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app _).app _ x = ((prod.fst : X ⨯ Y ⟶ X).app _).app _ y)
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ x = ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesLimitPair.iso G X Y ≪≫ Types.binaryProductIso (G.obj X) (G.obj Y)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  have a1 := (ConcreteCategory.congr_hom (prodComparison_fst G X Y))
  have a2 := (ConcreteCategory.congr_hom (prodComparison_snd G X Y))
  have b1 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_fst (G.obj X) (G.obj Y)))
  have b2 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_snd (G.obj X) (G.obj Y)))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b1 _).trans ((a1 x).trans (h1.trans ((a1 y).symm.trans (b1 _).symm)))
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b2 _).trans ((a2 x).trans (h2.trans ((a2 y).symm.trans (b2 _).symm)))

theorem um_basic {U : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(U, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) (p : U) :
    ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ U.basicOpen (v i) := by
  have h := iSup_basicOpen_of_span_eq_top (X := U) ⊤ (Set.range v) hv
  have hp : p ∈ (⊤ : U.Opens) := trivial
  rw [← h] at hp
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨⟨i, rfl⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  exact ⟨i, Nat.zero_le _, hi⟩

theorem basic_um {A : Type} [CommRing A] {N : ℕ} (v : Fin N → Γ(Spec (CommRingCat.of A), ⊤))
    (hv : ∀ p, ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ (Spec (CommRingCat.of A)).basicOpen (v i)) :
    Ideal.span (Set.range v) = ⊤ := by
  rw [← (isAffineOpen_top (Spec (CommRingCat.of A))).iSup_basicOpen_eq_self_iff]
  apply le_antisymm le_top
  intro p _
  obtain ⟨i, -, hi⟩ := hv p
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v i, i, rfl⟩, hi⟩

def cstV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤)))
      naturality := fun U U' g => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact (map_one (Matrix.GeneralLinearGroup.map _)).symm }
  naturality n m f := rfl

def conv {N n : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Um N Γ(U, ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : ComposableArrows (Vec N 0 U) n where
  obj i := ⟨(c.obj i).1, um_basic _ (c.obj i).2⟩
  map {i j} h := ⟨(c.map h).1.2, fun k => by
    have := congrFun (c.map h).2 k
    rw [hc h] at this
    simpa using this⟩
  map_id i := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_id i))
  map_comp f g := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_comp f g))

theorem conv_congr {N n : ℕ} {U : Scheme.{0}} {c c' : ComposableArrows (Um N Γ(U, ⊤)) n} (e : c = c')
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) : conv c hc = conv c' hc' := by
  subst e; rfl

theorem pb_gl {N : ℕ} {E : Spc} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}
    (x : ((pullback (cstV N E) (PGL.pr N)).obj n).obj U) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len).map h).1.1
      = 1 := by
  have e0 := ConcreteCategory.congr_hom
    (congrArg (fun φ : pullback (cstV N E) (PGL.pr N) ⟶ ofCat (glCat N) => (φ.app n).app U) (pullback.condition (f := cstV N E) (g := PGL.pr N))) x
  have e : ((Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(U.unop, ⊤))) n.unop.len) =
      (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len) ⋙
        Um.toGL N Γ(U.unop, ⊤) := e0
  have := Functor.congr_hom e.symm h
  exact this.trans ((Category.id_comp _).trans (Category.comp_id _))

def fMap (N : ℕ) (E : Spc) : pullback (cstV N E) (PGL.pr N) ⟶ Pj N 0 where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (conv (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) (pb_gl x) : ComposableArrows (Vec N 0 U.unop) n.unop.len)
      naturality := fun U U' g => by
        ext x
        have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U' (((pullback (cstV N E) (PGL.pr N)).obj n).map g x) :
            ComposableArrows (Um N Γ(U'.unop, ⊤)) n.unop.len) =
            ((PGL N).obj n).map g (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
          ConcreteCategory.congr_hom (((pullback.snd (cstV N E) (PGL.pr N)).app n).naturality g) x
        refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
        exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl)) }
  naturality n m f := by
    ext U x
    have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app m).app U (((pullback (cstV N E) (PGL.pr N)).map f).app U x) :
        ComposableArrows (Um N Γ(U.unop, ⊤)) m.unop.len) =
        ((PGL N).map f).app U (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
      ConcreteCategory.congr_hom (congrArg (fun φ : (pullback (cstV N E) (PGL.pr N)).obj n ⟶ (PGL N).obj m => φ.app U) ((pullback.snd (cstV N E) (PGL.pr N)).naturality f)) x
    refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

def back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n where
  obj i := ⟨(w.obj i).1, basic_um _ (w.obj i).2⟩
  map h := ⟨(1, (w.map h).1), by funext k; simpa using (w.map h).2 k⟩
  map_id i := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (one_mul 1).symm (congrArg Subtype.val (w.map_comp f g)))

theorem back_conv {A : Type} [CommRing A] {N n : ℕ} (c : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : back (conv c hc) = c :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ h => heq_of_eq (Subtype.ext (Prod.ext (hc h).symm rfl)))

theorem conv_back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    conv (back w) (fun _ => rfl) = w :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

theorem back_gl {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ((Functor.const (Fin (n + 1))).obj (SingleObj.star (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) n) = back w ⋙ Um.toGL N _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem conv_inj {A : Type} [CommRing A] {N n : ℕ} {c c' : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n}
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) (e : conv c hc = conv c' hc') : c = c' :=
  (back_conv c hc).symm.trans ((congrArg back e).trans (back_conv c' hc'))

theorem fMap_line (N : ℕ) (E : Spc) : fMap N E ≫ Pj.line N 0 = pullback.snd (cstV N E) (PGL.pr N) ≫ PGL.line N := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem eMap_bij (N : ℕ) (R : Type) [CommRing R] (n : ℕ) (A : Type) [CommRing A] : Function.Bijective
      (fun x : Sx (pullback (cstV N (sp R)) (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        ((prod.lift (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)) : _ ⟶ PR N 0 R).app
          (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x) := by
  have k1 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ Pj N 0 =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_fst (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  have k2 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ sp R =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_snd (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  constructor
  · intro x y hxy
    apply pb_ext
    · exact (k2 x).symm.trans ((congrArg _ hxy).trans (k2 y))
    · exact conv_inj (pb_gl x) (pb_gl y) ((k1 x).symm.trans ((congrArg _ hxy).trans (k1 y)))
  · intro z
    obtain ⟨x, hx1, hx2⟩ := pb_mk (cstV N (sp R)) (PGL.pr N) (n := n) (U := Spec (CommRingCat.of A))
      (((prod.snd : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z)
      (back (((prod.fst : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z))
      (back_gl _)
    refine ⟨x, pr_ext _ _ ?_ ?_⟩
    · exact (k1 x).trans ((conv_congr hx2 (pb_gl x) (fun _ => rfl)).trans (conv_back _))
    · exact (k2 x).trans hx1

theorem LeafPBMap_of : LeafPBMap := by
  set_option synthInstance.maxHeartbeats 100000 in
    exact fun N R _ =>
      ⟨cstV N (sp R), prod.lift (fMap N (sp R)) (pullback.fst _ _), prod.lift_snd _ _,
        by rw [prod.lift_fst_assoc]; exact fMap_line N (sp R), fun n A _ => eMap_bij N R n A⟩

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPbSumPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

theorem types_univ {A : Type} {F : Discrete A ⥤ Type} (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e _ H
  let i' : Discrete.functor (fun a => F'.obj ⟨a⟩) ≅ F' := Discrete.natIso (fun _ => Iso.refl _)
  let i : Discrete.functor (fun a => F.obj ⟨a⟩) ≅ F := Discrete.natIso (fun _ => Iso.refl _)
  let d : Cofan (fun a => F'.obj ⟨a⟩) := (Cocone.precompose i'.hom).obj c'
  let b : Cofan (fun a => F.obj ⟨a⟩) := (Cocone.precompose i.hom).obj c
  have hb : IsColimit b := (IsColimit.precomposeHomEquiv i c).symm hc
  have hd : ∀ a z, d.inj a z = c'.ι.app ⟨a⟩ z := fun _ _ => rfl
  have hbi : ∀ a z, b.inj a z = c.ι.app ⟨a⟩ z := fun _ _ => rfl
  have e1 : ∀ j x, c.ι.app j (α.app j x) = f (c'.ι.app j x) := fun j x => by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e j) x
    simpa using this
  refine ⟨(IsColimit.precomposeHomEquiv i' c') ((Cofan.nonempty_isColimit_iff_bijective_fromSigma d).2 ⟨?_, ?_⟩).some⟩
  · rintro ⟨a, z⟩ ⟨a', w⟩ h
    change d.inj a z = d.inj a' w at h
    rw [hd, hd] at h
    have h2 : b.inj a (α.app ⟨a⟩ z) = b.inj a' (α.app ⟨a'⟩ w) := by
      rw [hbi, hbi, e1, e1, h]
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hb _ _ h2
    have h3 := Cofan.inj_injective_of_isColimit hb a h2
    have := Types.ext_of_isPullback (H ⟨a⟩) h h3
    subst this
    rfl
  · intro y
    obtain ⟨a, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hb (f y)
    rw [hbi] at hx
    obtain ⟨z, hz1, _⟩ := Types.exists_of_isPullback (H ⟨a⟩) y x hx.symm
    exact ⟨⟨a, z⟩, hz1⟩

theorem univ_of_eval {J C D : Type*} [Category J] [Category C] [Category D] [HasPullbacks D]
    (F : J ⥤ C ⥤ D) (c : Cocone F)
    (hc : ∀ x : C, IsUniversalColimit (((evaluation C D).obj x).mapCocone c)) : IsUniversalColimit c := by
  intro F' c' α f e hα H
  exact ⟨evaluationJointlyReflectsColimits _ fun x =>
    (hc x (((evaluation C D).obj x).mapCocone c') (Functor.whiskerRight α _) (((evaluation C D).obj x).map f)
      (by ext y; dsimp; exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _) fun j => (H j).map ((evaluation C D).obj x)).some⟩

theorem spc_univ {A : Type} (F : Discrete A ⥤ Spc) (c : Cocone F) (hc : IsColimit c) : IsUniversalColimit c :=
  univ_of_eval (C := SimplexCategoryᵒᵖ) (D := PSh) F c fun n =>
    univ_of_eval (C := Scheme.{0}ᵒᵖ) (D := Type) _ _ fun Y =>
      types_univ _ (isColimitOfPreserves _ (isColimitOfPreserves ((evaluation _ _).obj n) hc))

theorem pb_of_eq {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f f' : X ⟶ Z} {g : Y ⟶ Z}
    (e : f = f') (hp : IsPullback fst snd f' g) : IsPullback fst snd f g := by subst e; exact hp

theorem pb_of_eq_snd {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd snd' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (e : snd = snd') (hp : IsPullback fst snd' f g) : IsPullback fst snd f g := by subst e; exact hp

end LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut
open PbSumPf

theorem LeafPbSum_of : LeafPbSum := by
  intro X U A E c hc π π' h
  have hS := (leafDiscSumH A E c hc).some
  have Uv := spc_univ _ _ hS
  let g := sch.map U.ι
  refine Uv (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
      fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left)
    (Discrete.natTrans fun a => pullback.fst (disc.map (π' a.as)) g)
    (pullback.fst (disc.map π) g) ?_ (.of_discrete _) ?_
  · apply NatTrans.ext; funext ⟨a⟩
    exact (pullback.lift_fst (f := disc.map π) (g := g) _ _ _).symm
  · rintro ⟨a⟩
    have outer : IsPullback (pullback.fst (disc.map (π' a)) g)
        ((abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g)
        (disc.map (c.inj a) ≫ disc.map π) g := by
      have e2 : (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g
          = pullback.snd (disc.map (π' a)) g := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
      exact pb_of_eq_snd e2 (pb_of_eq (h a) (IsPullback.of_hasPullback _ _))
    have sq := IsPullback.of_bot outer (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (disc.map π) g)
    exact sq.flip

end LateralTheory.CohomologicalPurity.TubeCut
end
end

