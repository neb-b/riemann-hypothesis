module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CmAugCocycle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section Cm

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E]
  (j : C' ⥤ C) (ι : E ⥤ C) (e : E)

def cmL : StructuredArrow (ι.obj e) j ⥤ StructuredArrow e (Comma.fst ι j) where
  obj y := StructuredArrow.mk (Y := (⟨e, y.right, y.hom⟩ : Comma ι j)) (𝟙 e)
  map {y y'} f := StructuredArrow.homMk ⟨𝟙 e, f.right, by simp [StructuredArrow.w f]⟩ (by simp)
  map_id y := by ext <;> simp
  map_comp f g := by ext <;> simp

def cmU : StructuredArrow e (Comma.fst ι j) ⥤ StructuredArrow (ι.obj e) j where
  obj x := StructuredArrow.mk (Y := x.right.right) (ι.map x.hom ≫ x.right.hom)
  map {x x'} f := StructuredArrow.homMk f.right.right (by
    have h2 := StructuredArrow.w f
    dsimp at h2 ⊢
    rw [Category.assoc, ← f.right.w, ← Category.assoc, ← ι.map_comp, show x.hom ≫ f.right.left = x'.hom from h2])
  map_id x := by ext; simp
  map_comp f g := by ext; simp

theorem cm_w {y : StructuredArrow (ι.obj e) j} {x : StructuredArrow e (Comma.fst ι j)} (g : (cmL j ι e).obj y ⟶ x) :
    g.right.left = x.hom := by
  have h2 := StructuredArrow.w g
  dsimp [cmL] at h2
  simpa using h2

def cmAdj : cmL j ι e ⊣ cmU j ι e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun y x =>
        { toFun := fun g => StructuredArrow.homMk g.right.right (by
            dsimp [cmL, cmU]
            rw [← cm_w j ι e g]
            exact g.right.w.symm)
          invFun := fun f => StructuredArrow.homMk
            { left := x.hom, right := f.right, w := (StructuredArrow.w f).symm } (by dsimp [cmL]; simp)
          left_inv := fun g => by
            apply StructuredArrow.ext
            apply Comma.hom_ext
            · exact (cm_w j ι e g).symm
            · rfl
          right_inv := fun f => by
            apply StructuredArrow.ext
            rfl }
      homEquiv_naturality_left_symm := by
        intro y' y x f g
        apply StructuredArrow.ext
        apply Comma.hom_ext
        all_goals (dsimp [cmL]; try simp)
      homEquiv_naturality_right := by
        intro y x x' f g
        apply StructuredArrow.ext
        dsimp [cmU]
        try simp }

end Cm

def cmMor {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''}
    [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (e : E) :
    Mor (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
      (StructuredArrow.proj (ι.obj e) j ⋙ j ⋙ F) (RingHom.id R) where
  G := cmL j ι e
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem cm_aug_cocycle {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (T : C) (a : F.obj T) :
    d (StructuredArrow.proj T m.G ⋙ F') 0
      (aug (StructuredArrow.proj T m.G ⋙ F') (fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom) a) = 0 := by
  rw [← fib_aug m T]
  have := (relMor (𝟭 C) m T).hom.comm 0
    (aug (relF (𝟭 C) F T) (fun T' => ((relF (𝟭 C) F T).map ((fib_init T).to T')).hom) a)
  have h0 := (CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)).1 a
  exact this.trans ((congrArg _ h0).trans (map_zero _))

theorem cm_transfer {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (hb : ∀ n, Function.Bijective (φ.mapH n)) {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0)
    (hd : ∀ x, K.d 0 (ε x) = 0) (s : R) (hL : L.ResUpTo s (φ.f 0 ∘ₗ ε)) : K.ResUpTo s ε := by
  have h1 : ∀ n, UpTo (1 : R) (φ.mapH n) := fun n =>
    ((CrystallineSemistableComparison.P.upTo_alg (φ.mapH n) LinearMap.id (1 : R) 1).2.2.2.2).2 (hb n)
  have := (CrystallineSemistableComparison.P.res_transfer φ ε s 1 h1).2 hd hL
  rwa [mul_one] at this

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.comma1 : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (s : R) (h : ∀ {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)), (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a)), Desc s F j → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) := by
  intro R _ C _ C' _ E _ F j ι s h hD n
  refine CrystallineSemistableComparison.B.P.fib _ s (fun e => ?_) n
  have : (CrystallineSemistableComparison.B.cmMor F j ι e).G.IsLeftAdjoint := (CrystallineSemistableComparison.B.cmAdj j ι e).isLeftAdjoint
  refine CrystallineSemistableComparison.B.cm_transfer (CrystallineSemistableComparison.B.cmMor F j ι e).hom
    (fun k => CrystallineSemistableComparison.P.adj_mor (CrystallineSemistableComparison.B.cmMor F j ι e) (fun _ => Function.bijective_id) k) _
    (CrystallineSemistableComparison.B.cm_aug_cocycle (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) e) s ?_
  have eq : (CrystallineSemistableComparison.B.cmMor F j ι e).hom.f 0 ∘ₗ
      (aug (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
        fun x => (F.map x.right.hom).hom ∘ₗ ((ι ⋙ F).map x.hom).hom) = unAug F j (ι.obj e) := by
    apply LinearMap.ext; intro a; funext c
    change (F.map (c.obj (Fin.last 0)).hom).hom ((F.map (ι.map (𝟙 e))).hom a) = (F.map (c.obj (Fin.last 0)).hom).hom a
    rw [ι.map_id, F.map_id]
    rfl
  exact eq ▸ hD (ι.obj e)
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FFible
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem fible_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (q : ℕ)
    (s₁ s₂ : R) (hK : ExactUpTo s₁ (K.d q) (K.d (q + 1))) (hφ : SurjUpTo s₂ (φ.mapH (q + 1))) :
    ExactUpTo (s₁ * s₂) (L.d q) (L.d (q + 1)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hφ (L.cls y hy)
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (q + 1)).1 x
  obtain ⟨c, hc⟩ := hK b hb
  have hfb : L.d (q + 1) (φ.f (q + 1) b) = 0 := by rw [φ.comm, hb, map_zero]
  have hy2 : L.d (q + 1) (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
  have hy12 : L.d (q + 1) (s₁ • s₂ • y) = 0 := by rw [map_smul, hy2, smul_zero]
  have hs1b : L.d (q + 1) (s₁ • φ.f (q + 1) b) = 0 := by rw [map_smul, hfb, smul_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ (q + 1) b hb hfb, ← resLe_cls_smul L (q + 1) s₂ y hy hy2] at hx
  have e1 : L.cls (s₁ • s₂ • y) hy12 = L.cls (s₁ • φ.f (q + 1) b) hs1b := by
    rw [resLe_cls_smul L (q + 1) s₁ _ hfb hs1b, hx, ← resLe_cls_smul L (q + 1) s₁ _ hy2 hy12]
  have e2 : L.cls (s₁ • φ.f (q + 1) b) hs1b = 0 := by
    refine resLe_cls_zero L (q + 1) _ hs1b ⟨φ.f q c, ?_⟩
    rw [φ.comm, hc, map_smul]
  rw [e2] at e1
  obtain ⟨c', hc'⟩ := ((CrystallineSemistableComparison.P.cls_surj L (q + 1)).2.1 _ hy12).1 e1
  exact ⟨c', by rw [hc', mul_smul]⟩

theorem fible_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {A : Type u''} [AddCommGroup A] [Module R A] (ε : A →ₗ[R] K.X 0) (hd : ∀ x, K.d 0 (ε x) = 0) (s₁ s₂ : R)
    (hi : InjUpTo s₁ ε) (he : ExactUpTo s₁ ε (K.d 0)) (hφ : UpTo s₂ (φ.mapH 0)) :
    InjUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) ∧ ExactUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) (L.d 0) := by
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
      exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
    have h2 := hφ.1 _ h1
    have hs' : K.d 0 (s₂ • ε x) = 0 := by rw [map_smul, hd, smul_zero]
    rw [← resLe_cls_smul K 0 s₂ _ _ hs'] at h2
    have h3 : s₂ • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
    rw [← map_smul] at h3
    rw [mul_smul]
    exact hi _ h3
  · obtain ⟨x, hx⟩ := hφ.2 (L.cls y hy)
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
    obtain ⟨a, ha⟩ := he b hb
    refine ⟨a, ?_⟩
    have hy' : L.d 0 (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
    have hfb : L.d 0 (φ.f 0 b) = 0 := by rw [φ.comm, hb, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ 0 b hb hfb, ← resLe_cls_smul L 0 s₂ y hy hy'] at hx
    have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfb hy').1 hx
    have h4 : φ.f 0 b = s₂ • y := sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
    change φ.f 0 (ε a) = _
    rw [ha, map_smul, h4, mul_smul]

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.fible : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (s : R) (n : ℕ), (∀ T : C, ∃ (E : Type v'') (_ : Category.{u''} E) (M : E ⥤ ModuleCat.{w} R) (μ : Mor M (StructuredArrow.proj T m.G ⋙ F') (RingHom.id R)) (e : ∀ x : E, F.obj T →ₗ[R] M.obj x) (s₁ s₂ : R), s = s₁ * s₂ ∧ (∀ x a, μ.τ x (e _ a) = m.τ x.right ((F.map x.hom).hom a)) ∧ (∀ (x y : E) (φ : x ⟶ y) a, (M.map φ).hom (e x a) = e y a) ∧ IsoLe s₂ (n + 1) μ ∧ InjUpTo s₁ (aug M e) ∧ ExactUpTo s₁ (aug M e) (d M 0) ∧ ∀ j ≤ n, ExactUpTo s₁ (d M j) (d M (j + 1))) → IsoLe (s ^ (2 * n + 3)) n m := by
  intro R _ C _ C' _ F F' m s n hT
  have key : ∀ (T : C), ∀ q ≤ n + 1, UpTo s ((relMor (𝟭 C) m T).pull q) := by
    intro T q hq
    obtain ⟨E, _, M, μ, e, s₁, s₂, rfl, hμe, he, hiso, hinj, hex0, hex⟩ := hT T
    have hK := CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)
    cases q with
    | zero =>
      refine (resLe_zero (relMor (𝟭 C) m T).hom _ hK _).2 ?_
      have hd : ∀ a, d M 0 (aug M e a) = 0 := by
        intro a; funext c
        change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (M.map (GlobalTheory.CatH.toLast i c)).hom (e _ a) = 0
        simp only [he, Fin.sum_univ_two]
        simp
      have eqε : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
          aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
          μ.hom.f 0 ∘ₗ aug M e := by
        have e1 : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
            aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
            aug (relF (m.G ⋙ 𝟭 C) F' T) fun x => ((relMor (𝟭 C) m T).τ x) ∘ₗ
              ((relF (𝟭 C) F T).map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj x))).hom :=
          LinearMap.ext fun a => funext fun c => rfl
        rw [e1, fib_aug]
        apply LinearMap.ext; intro a; funext c
        exact (hμe _ a).symm
      rw [eqε]
      exact fible_zero μ.hom (aug M e) hd s₁ s₂ hinj hex0 (hiso 0 (Nat.zero_le _))
    | succ q =>
      refine (resLe_succ (relMor (𝟭 C) m T).hom q (hK.2.2.2 q) _).2 ?_
      exact fible_succ μ.hom q s₁ s₂ (hex q (by omega)) (hiso (q + 1) (by omega)).2
  intro j hj
  have h1 := CrystallineSemistableComparison.P.rel (𝟭 C) m s j (fun i q hq => key i q (by omega))
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have e : s ^ (2 * (j + k) + 3) = s ^ (2 * j + 3) * s ^ (2 * k) := by rw [← pow_add]; ring_nf
  rw [e]
  exact (CrystallineSemistableComparison.P.upTo_alg (m.pull j) LinearMap.id _ _).2.2.2.1 h1
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlob
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_onto {D : Type u} [Category.{v} D] {D₁ : Type u'} [Category.{v'} D₁] (Z : ObjectProperty D)
    (κ : D₁ ⥤ D) (hκ : ∀ T, Z (κ.obj T)) (W : D → Prop) (h : Onto κ W) :
    Onto (Z.lift κ hκ) (fun T => W T.obj) := by
  have : κ.Full := h.full
  have : κ.Faithful := h.faithful
  have : (Z.lift κ hκ ⋙ Z.ι).Full := h.full
  have : (Z.lift κ hκ ⋙ Z.ι).Faithful := h.faithful
  refine ⟨Functor.Full.of_comp_faithful _ Z.ι, Functor.Faithful.of_comp _ Z.ι, fun T => h.mem T, ?_⟩
  intro T hT
  obtain ⟨T₁, ⟨f⟩⟩ := h.ess T.obj hT
  exact ⟨T₁, ⟨Z.ι.preimageIso f⟩⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glob : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → RI 1 n F (ObjectProperty.ι fun T => ∃ α, Q α T) → RI 1 n (G ⋙ F) (ObjectProperty.ι fun T => ∃ α, Q α (G.obj T)) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hP hP' hS
  let Pr : ObjectProperty C := fun T => ∃ α, Q α T
  let Pr' : ObjectProperty C' := fun T => ∃ α, Q α (G.obj T)
  let Gq : Pr'.FullSubcategory ⥤ Pr.FullSubcategory := Pr.lift (Pr'.ι ⋙ G) (fun T => T.property)
  let Fq : Pr.FullSubcategory ⥤ ModuleCat.{w} R := Pr.ι ⋙ F
  have hc : RI (s ^ (2 * n + 3)) n Fq Gq := by
    refine P.chart Fq Gq (fun α T => Q α T.obj) s n (fun α T T' f h => hQ α f.hom h) (fun T => T.property) ?_
    intro S hSn
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S hSn
    obtain ⟨α₀, hα₀⟩ := hSn
    let ιq : C₁ ⥤ Pr.FullSubcategory := Pr.lift ι (fun T => ⟨α₀, hO.mem T α₀ hα₀⟩)
    let ιq' : C₁' ⥤ Pr'.FullSubcategory := Pr'.lift ι' (fun T => ⟨α₀, hO'.mem T α₀ hα₀⟩)
    refine ⟨C₁, inferInstance, C₁', inferInstance, ιq, ιq', G₁, ?_, ?_, ?_, hR⟩
    · exact gl_onto Pr ι _ (fun T => ∀ α ∈ S, Q α T) hO
    · exact gl_onto Pr' ι' _ (fun T => ∀ α ∈ S, Q α (G.obj T)) hO'
    · exact ⟨Functor.fullyFaithfulCancelRight Pr.ι e⟩
  have h1 : RI (1 * s ^ (2 * n + 3)) n F (Gq ⋙ Pr.ι) := (P.ri_calc F Pr.ι Gq 1 _ n).1 hP hc
  have h2 : RI (1 * (1 * s ^ (2 * n + 3))) n F G := (P.ri_calc F G Pr'.ι 1 _ n).2.2.1 hP' h1
  rwa [one_mul, one_mul] at h2
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FKstep
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem kstep_aug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    d F 0 (aug F e x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (e _ x) = 0
  simp only [he, Fin.sum_univ_two]
  simp

def kstepLast (d k : ℕ) : Gam (d + 1) := Multiplicative.ofAdd (Pi.single (Fin.last d) k)

section kstep

variable {d : ℕ} (π : Gam (d + 1) →* Gam d)
  (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc)

include hπ in
theorem kstep_π_last (k : ℕ) : π (kstepLast d k) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepLast, Fin.castSucc_ne_last]

def kstepL (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) : SingleObj (Multiplicative ℕ) ⥤ StructuredArrow (SingleObj.star (Gam d)) π.toFunctor where
  obj _ := StructuredArrow.mk (Y := SingleObj.star (Gam (d + 1)))
    (show SingleObj.star (Gam d) ⟶ π.toFunctor.obj (SingleObj.star _) from (1 : Gam d))
  map k := StructuredArrow.homMk (show SingleObj.star (Gam (d + 1)) ⟶ SingleObj.star _ from
      kstepLast d (Multiplicative.toAdd k)) (by
    simp only [StructuredArrow.mk_hom_eq_self]
    exact kstep_π_last π hπ _)
  map_id _ := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd (1 : Multiplicative ℕ)) = (1 : Gam (d + 1))
    simp [kstepLast]
  map_comp f g := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) = kstepLast d (Multiplicative.toAdd (g : Multiplicative ℕ)) * kstepLast d (Multiplicative.toAdd (f : Multiplicative ℕ))
    simp [kstepLast, Pi.single_add]

def kstepU : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ SingleObj (Multiplicative ℕ) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
  map_id _ := by
    change Multiplicative.ofAdd (Multiplicative.toAdd (1 : Gam (d + 1)) (Fin.last d)) = 1
    simp
  map_comp f g := by
    change Multiplicative.ofAdd (Multiplicative.toAdd ((show Gam (d + 1) from g.right) * (show Gam (d + 1) from f.right)) (Fin.last d)) =
      Multiplicative.ofAdd (Multiplicative.toAdd (g.right : Gam (d + 1)) (Fin.last d)) *
        Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
    simp only [toAdd_mul, Pi.add_apply, ofAdd_add]
    rfl

def kstepSnoc (b : Gam d) (k : ℕ) : Gam (d + 1) :=
  Multiplicative.ofAdd (Fin.snoc (α := fun _ => ℕ) (Multiplicative.toAdd b) k)

include hπ in
theorem kstep_π_snoc (b : Gam d) (k : ℕ) : π (kstepSnoc b k) = b := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepSnoc]

include hπ in
theorem kstep_snoc_eq (a : Gam (d + 1)) : kstepSnoc (π a) (Multiplicative.toAdd a (Fin.last d)) = a := by
  apply Multiplicative.toAdd.injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [kstepSnoc]
  | cast i => simp [kstepSnoc, hπ]

def kstepAdj : kstepL π hπ ⊣ kstepU π :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => show X ⟶ (kstepU π).obj Y from
            Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
          invFun := fun k => StructuredArrow.homMk
            (show ((kstepL π hπ).obj X).right ⟶ Y.right from
              kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k)))
            (kstep_π_snoc π hπ _ _)
          left_inv := fun f => by
            apply StructuredArrow.hom_ext
            change kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d)) = f.right
            have w : (show Gam d from Y.hom) = π f.right := (StructuredArrow.w f).symm
            rw [w]
            exact kstep_snoc_eq π hπ _
          right_inv := fun k => by
            change Multiplicative.ofAdd (Multiplicative.toAdd
              (kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k))) (Fin.last d)) = k
            simp [kstepSnoc] }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply StructuredArrow.hom_ext
        change kstepSnoc (show Gam d from Y.hom)
            (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) =
          kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from g)) *
            kstepLast d (Multiplicative.toAdd (show Multiplicative ℕ from f))
        apply Multiplicative.toAdd.injective
        funext i
        induction i using Fin.lastCases with
        | last => simp [kstepSnoc, kstepLast]
        | cast i => simp [kstepSnoc, kstepLast, Fin.castSucc_ne_last]
      homEquiv_naturality_right := fun f g => (kstepU π).map_comp f g }

end kstep

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.kstep : ∀ {R : Type} [CommRing R] {d : ℕ} (M : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (N : SingleObj (Gam (d + 1)) ⥤ ModuleCat.{w} R) (π : Gam (d + 1) →* Gam d) (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) (τ : M.obj (SingleObj.star _) →ₗ[R] N.obj (SingleObj.star _)) (h : ∀ (a : Gam (d + 1)) x, τ ((M.map (X := SingleObj.star _) (Y := SingleObj.star _) (π a)).hom x) = (N.map (X := SingleObj.star _) (Y := SingleObj.star _) a).hom (τ x)) (s : R), Acyc1 s τ (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨π.toFunctor, fun _ => τ, fun φ x => h φ x⟩ : Mor M N (RingHom.id R)) := by
  intro R _ d M N π hπ τ h s hA n
  apply CrystallineSemistableComparison.B.P.fib
  intro T
  have hM1 : M.map (X := SingleObj.star _) (Y := SingleObj.star _) (1 : Gam d) = 𝟙 _ := M.map_id _
  obtain rfl : T = SingleObj.star (Gam d) := Subsingleton.elim _ _
  let F' : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ ModuleCat.{w} R :=
    StructuredArrow.proj (SingleObj.star (Gam d)) π.toFunctor ⋙ N
  let e : ∀ x : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor,
      M.obj (SingleObj.star (Gam d)) →ₗ[R] F'.obj x := fun x => τ ∘ₗ (M.map x.hom).hom
  have he : ∀ {x y : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor} (φ : x ⟶ y) a,
      (F'.map φ).hom (e x a) = e y a := by
    intro x y φ a
    have h1 := h φ.right ((M.map x.hom).hom a)
    refine h1.symm.trans ?_
    change τ ((M.map x.hom ≫ M.map (π.toFunctor.map φ.right)).hom a) = τ ((M.map y.hom).hom a)
    rw [← M.map_comp, StructuredArrow.w φ]
  have hfix : ∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom (τ x) = τ x := by
    intro x
    rw [← h, show π (gen (Fin.last d)) = 1 from kstep_π_last π hπ 1, hM1]
    rfl
  have hb := CrystallineSemistableComparison.B.P.bnat (kstepL π hπ ⋙ F') τ s hfix hA
  have hadj := CrystallineSemistableComparison.P.adj F' (kstepL π hπ) (kstepU π) (kstepAdj π hπ)
  have hup : ∀ k, UpTo (1 : R) ((Mor.restrict F' (kstepL π hπ)).hom.mapH k) := fun k =>
    ((CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) (1 : R) 1).2.2.2.2).2 (hadj k)
  have hε : (Mor.restrict F' (kstepL π hπ)).hom.f 0 ∘ₗ aug F' e = aug (kstepL π hπ ⋙ F') fun _ => τ := by
    refine LinearMap.ext fun x => funext fun s => ?_
    change τ ((M.map (1 : Gam d)).hom x) = τ x
    rw [hM1]
    rfl
  have htr := (CrystallineSemistableComparison.P.res_transfer (Mor.restrict F' (kstepL π hπ)).hom (aug F' e) s 1 hup).2
    (kstep_aug_d F' e he) (hε ▸ hb)
  rw [mul_one] at htr
  exact htr
end

