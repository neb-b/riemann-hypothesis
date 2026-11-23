module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZariskiNoetherianInduction
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AddIff
section
noncomputable section

open CategoryTheory Opposite

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private def pre {A : C} (S : Fam A) : Presieve (op A : Cᵒᵖ) :=
  Presieve.ofArrows (fun i => op (S.B i)) (fun i => (S.f i).op)

private def cov (Pa : Parts C) : Coverage Cᵒᵖ where
  coverings X := {R | ∃ S : Fam X.unop, Pa.Cov S ∧ R = pre S}
  pullback := by
    rintro X Y f R ⟨S, hS, rfl⟩
    obtain ⟨B', f', ψ, hc, hcomm⟩ := Pa.pull f.unop S hS
    refine ⟨_, ⟨⟨S.ι, B', f'⟩, hc, rfl⟩, ?_⟩
    rintro Z g ⟨i⟩
    refine ⟨op (S.B i), (ψ i).op, (S.f i).op, Presieve.ofArrows.mk i, ?_⟩
    apply Quiver.Hom.unop_inj
    simpa using hcomm i

private abbrev Jt (Pa : Parts C) : GrothendieckTopology Cᵒᵖ := (cov Pa).toGrothendieck

private theorem add_iff (Pa : Parts C) (F : Coef C) :
    Pa.Add F ↔ Presheaf.IsSheaf (Jt Pa) (unopUnop C ⋙ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat.{1}),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  constructor
  · rintro h X R ⟨S, hS, rfl⟩
    refine (Presieve.isSheafFor_arrows_iff _ _).2 fun x _ => ?_
    obtain ⟨t, ht⟩ := (h _ S hS).2 x
    exact ⟨t, fun i => congrFun ht i,
      fun t' ht' => (h _ S hS).1 (funext fun i => (ht' i).trans (congrFun ht i).symm)⟩
  · intro h A S hS
    have arrows : ∀ {X : C} (S : Fam X), Pa.Cov S → ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x → ∃! t, ∀ i, (F.map (S.f i)).hom t = x i :=
      fun {X} S hS x hx =>
        (Presieve.isSheafFor_arrows_iff _ _).1 (h (X := op X) (pre S) ⟨S, hS, rfl⟩) x hx
    have sub : ∀ X : C, Pa.Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam X) →
        Subsingleton (F.obj X) := fun X hX => ⟨fun a b =>
      (arrows _ hX (fun e => e.elim) (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)⟩
    have compat : ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x := by
      intro x i j Z gi gj e
      have e' : S.f i ≫ gi.unop = S.f j ≫ gj.unop := congrArg Quiver.Hom.unop e
      by_cases hij : i = j
      · subst hij
        have : gi.unop = gj.unop := (Pa.epi S hS i).left_cancellation _ _ e'
        rw [Quiver.Hom.unop_inj this]
      · have := sub _ (Pa.disj S hS hij gi.unop gj.unop e')
        exact Subsingleton.elim (α := F.obj Z.unop) _ _
    constructor
    · intro a b hab
      exact (arrows S hS _ (compat fun i => (F.map (S.f i)).hom a)).unique (fun i => rfl)
        (fun i => (congrFun hab i).symm)
    · intro x
      obtain ⟨t, ht, -⟩ := arrows S hS x (compat x)
      exact ⟨t, funext ht⟩

private theorem enough (Pa : Parts C) : EnoughInjectives (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
  haveI : EssentiallySmall.{1} Cᵒᵖ := essentiallySmall_of_small_of_locallySmall _
  haveI : IsGrothendieckAbelian.{1} (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  inferInstance

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.emb :
    UpperTheory.Ru.crystallineComparison.Emb := by
  intro C _ Pa F hF
  haveI := enough Pa
  let Fs : Sheaf (Jt Pa) AddCommGrpCat.{1} := ⟨unopUnop C ⋙ F, (add_iff Pa F).1 hF⟩
  let I := Injective.under Fs
  let G := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).obj I
  have hG : Presheaf.IsSheaf (Jt Pa) G := I.property
  haveI inj : Injective G :=
    Injective.injective_of_adjoint (sheafificationAdjunction (Jt Pa) AddCommGrpCat.{1}) I
  let m := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).map (Injective.ι Fs)
  have hm : Mono m := inferInstance
  refine ⟨opOp C ⋙ G, { app := fun X => m.app (op (op X)), naturality := fun X Y f => m.naturality f.op.op }, ?_, ?_, ?_⟩
  · rw [NatTrans.mono_iff_mono_app]
    intro X
    exact (NatTrans.mono_iff_mono_app m).1 hm _
  · exact Injective.injective_of_adjoint
      ((opOpEquivalence C).congrLeft (E := AddCommGrpCat.{1})).symm.toAdjunction G
  · exact (add_iff Pa _).2 hG
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EvalExact
section
open CategoryTheory

namespace UpperTheory.Ru.crystallineComparison

private lemma evalExact {C : Type 1} [Category.{0} C] (S : ShortComplex (Coef C))
    (h : S.ShortExact) (B : C) :
    Function.Exact (S.f.app B).hom (S.g.app B).hom ∧
      Function.Injective (S.f.app B).hom ∧ Function.Surjective (S.g.app B).hom := by
  have hB := h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj B)
  have hm := hB.mono_f
  have he := hB.epi_g
  exact ⟨(ShortComplex.ab_exact_iff_function_exact _).1 hB.exact,
    (AddCommGrpCat.mono_iff_injective _).1 hm, (AddCommGrpCat.epi_iff_surjective _).1 he⟩

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.quotAdd :
    UpperTheory.Ru.crystallineComparison.QuotAdd := by
  intro C _ Pa S hS h1 h2 A T hT
  have ex := fun B => UpperTheory.Ru.crystallineComparison.evalExact S hS B
  have natf : ∀ (i : T.ι) (z : S.X₁.obj A),
      (S.f.app (T.B i)).hom ((S.X₁.map (T.f i)).hom z) =
        (S.X₂.map (T.f i)).hom ((S.f.app A).hom z) := by
    intro i z
    have := congrArg (fun φ => φ.hom z) (S.f.naturality (T.f i))
    simpa using this
  have natg : ∀ (i : T.ι) (y : S.X₂.obj A),
      (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) =
        (S.X₃.map (T.f i)).hom ((S.g.app A).hom y) := by
    intro i y
    have := congrArg (fun φ => φ.hom y) (S.g.naturality (T.f i))
    simpa using this
  have inj0 : ∀ x : S.X₃.obj A, (∀ i, (S.X₃.map (T.f i)).hom x = 0) → x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (ex A).2.2 x
    have hz : ∀ i, ∃ z : S.X₁.obj (T.B i),
        (S.f.app (T.B i)).hom z = (S.X₂.map (T.f i)).hom y := by
      intro i
      have : (S.g.app (T.B i)).hom ((S.X₂.map (T.f i)).hom y) = 0 := by
        rw [natg]; exact hx i
      exact ((ex (T.B i)).1 _).1 this
    choose z hz using hz
    obtain ⟨w, hw⟩ := (h1 A T hT).2 z
    have hy : y = (S.f.app A).hom w := by
      apply (h2 A T hT).1
      funext i
      show (S.X₂.map (T.f i)).hom y = (S.X₂.map (T.f i)).hom ((S.f.app A).hom w)
      rw [← natf, ← hz i]
      exact congrArg _ (congrFun hw i).symm
    rw [hy]
    exact ((ex A).1 _).2 ⟨w, rfl⟩
  constructor
  · intro x x' e
    rw [← sub_eq_zero]
    apply inj0
    intro i
    have := congrFun e i
    simp only at this
    rw [map_sub, this, sub_self]
  · intro v
    have hy : ∀ i, ∃ y : S.X₂.obj (T.B i), (S.g.app (T.B i)).hom y = v i :=
      fun i => (ex (T.B i)).2.2 (v i)
    choose y hy using hy
    obtain ⟨w, hw⟩ := (h2 A T hT).2 y
    refine ⟨(S.g.app A).hom w, ?_⟩
    funext i
    show (S.X₃.map (T.f i)).hom ((S.g.app A).hom w) = v i
    rw [← natg, ← hy i]
    exact congrArg _ (congrFun hw i)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceSnocCastSucc
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

section Snoc

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

def snObj (X : E) (i : Fin (m + 2)) : E := if h : (i : ℕ) < m + 1 then s.obj ⟨i, h⟩ else X

theorem snObj_lt (X : E) {i : Fin (m + 2)} (h : (i : ℕ) < m + 1) : snObj s X i = s.obj ⟨i, h⟩ := dif_pos h

theorem snObj_ge (X : E) {i : Fin (m + 2)} (h : ¬ (i : ℕ) < m + 1) : snObj s X i = X := dif_neg h

def snMap (i j : Fin (m + 2)) (hij : i ≤ j) : snObj s X i ⟶ snObj s X j :=
  if hj : (j : ℕ) < m + 1 then
    eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm
  else if hi : (i : ℕ) < m + 1 then
    eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm
  else eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm)

theorem snMap_lt {i j : Fin (m + 2)} (hij : i ≤ j) (hj : (j : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm := dif_pos hj

theorem snMap_mid {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm := by
  rw [snMap, dif_neg hj, dif_pos hi]

theorem snMap_top {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : ¬ (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm) := by
  rw [snMap, dif_neg hj, dif_neg hi]

def snoc : ComposableArrows E (m + 1) where
  obj := snObj s X
  map {i j} f := snMap s a i j (leOfHom f)
  map_id i := by
    by_cases hi : (i : ℕ) < m + 1
    · rw [snMap_lt s a _ hi]
      simp [homOfLE_refl]
    · rw [snMap_top s a _ hi hi]
      simp
  map_comp {i j k} f g := by
    have hij := leOfHom f
    have hjk := leOfHom g
    by_cases hk : (k : ℕ) < m + 1
    · have hj : (j : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hjk) hk
      rw [snMap_lt s a _ hk, snMap_lt s a _ hk, snMap_lt s a _ hj]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Functor.map_comp_assoc]
      rfl
    · by_cases hj : (j : ℕ) < m + 1
      · have hi : (i : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hij) hj
        rw [snMap_mid s a _ hk hi, snMap_mid s a _ hk hj, snMap_lt s a _ hj]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Functor.map_comp_assoc]
        rfl
      · by_cases hi : (i : ℕ) < m + 1
        · rw [snMap_mid s a _ hk hi, snMap_mid s a _ hj hi, snMap_top s a _ hk hj]
          simp
        · rw [snMap_top s a _ hk hi, snMap_top s a _ hj hi, snMap_top s a _ hk hj]
          simp

theorem snoc_last : (snoc s a).obj (Fin.last (m + 1)) = X := snObj_ge s X (by simp)

end Snoc
section Chains

variable {E : Type*} [Category E]

theorem chain_ext {n : ℕ} {T T' : ComposableArrows E n} (ho : ∀ i, T.obj i = T'.obj i)
    (hm : ∀ i j (h : i ≤ j), T.map (homOfLE h) = eqToHom (ho i) ≫ T'.map (homOfLE h) ≫ eqToHom (ho j).symm) : T = T' :=
  CategoryTheory.Functor.ext ho fun i j f => hm i j (leOfHom f)

theorem sigma_chain_eq {n : ℕ} {X : E} {s s' : ComposableArrows E n} {b : s.obj (Fin.last n) ⟶ X}
    {b' : s'.obj (Fin.last n) ⟶ X} (h : s = s') (w : b = eqToHom (by rw [h]) ≫ b') :
    (⟨s, b⟩ : Σ t : ComposableArrows E n, t.obj (Fin.last n) ⟶ X) = ⟨s', b'⟩ := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at w
  rw [w]

variable {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

theorem snObj_val {p : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) : snObj s X p = s.obj q :=
  (snObj_lt s X (h ▸ q.2)).trans (congrArg s.obj (Fin.ext h))

theorem snMap_val {p p' : Fin (m + 2)} {q q' : Fin (m + 1)} (h : (p : ℕ) = q) (h' : (p' : ℕ) = q') (hp : p ≤ p') (hq : q ≤ q') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE hq) ≫ eqToHom (snObj_val s h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain ⟨q', hq1⟩ := q'
  obtain rfl : (p : ℕ) = q := h
  obtain rfl : (p' : ℕ) = q' := h'
  exact snMap_lt s a hp hq1

theorem snMap_val_top {p p' : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) (h' : ¬ (p' : ℕ) < m + 1) (hp : p ≤ p') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE (Fin.le_last q)) ≫ a ≫ eqToHom (snObj_ge s X h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain rfl : (p : ℕ) = q := h
  exact snMap_mid s a hp h' hq0

def snε : (snoc s a).obj (Fin.last (m + 1)) ⟶ X := eqToHom (snoc_last s a)

theorem face_snoc_last : face (Fin.last (m + 1)) (snoc s a) = s := by
  have hv : ∀ i : Fin (m + 1), (((Fin.last (m + 1)).succAbove i : Fin (m + 2)) : ℕ) = i := fun i => by simp
  refine chain_ext (fun i => snObj_val s (hv i)) fun i j h => ?_
  exact snMap_val s a (hv i) (hv j) ((Fin.strictMono_succAbove _).monotone h) h

theorem gen_snoc_last :
    (⟨face (Fin.last (m + 1)) (snoc s a), toLast (Fin.last (m + 1)) (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E m, t.obj (Fin.last m) ⟶ X) = ⟨s, a⟩ := by
  refine sigma_chain_eq (face_snoc_last s a) ?_
  have hv : (((Fin.last (m + 1)).succAbove (Fin.last m) : Fin (m + 2)) : ℕ) = (Fin.last m : Fin (m + 1)) := by simp
  have e : toLast (Fin.last (m + 1)) (snoc s a) = eqToHom (snObj_val s hv) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫
      eqToHom (snObj_ge s X (by simp)).symm := snMap_val_top s a hv (by simp) (Fin.le_last _)
  rw [e]
  simp [snε, homOfLE_refl]

theorem snoc_reindex {n : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : Monotone f) (g : Fin (n + 2) → Fin (m + 2)) (hg : Monotone g)
    (h1 : ∀ (p : Fin (n + 2)) (hp : (p : ℕ) < n + 1), (g p : ℕ) = f ⟨p, hp⟩)
    (h2 : ∀ p : Fin (n + 2), ¬ (p : ℕ) < n + 1 → ¬ (g p : ℕ) < m + 1) :
    hg.functor ⋙ snoc s a = snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) := by
  have ho : ∀ p, (hg.functor ⋙ snoc s a).obj p = (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).obj p := by
    intro p
    by_cases hp : (p : ℕ) < n + 1
    · exact (snObj_val s (h1 p hp)).trans (snObj_lt (hf.functor ⋙ s) X hp).symm
    · exact (snObj_ge s X (h2 p hp)).trans (snObj_ge (hf.functor ⋙ s) X hp).symm
  refine chain_ext ho fun p p' h => ?_
  have e1 : (hg.functor ⋙ snoc s a).map (homOfLE h) = snMap s a (g p) (g p') (hg h) := rfl
  have e2 : (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).map (homOfLE h) =
    snMap (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) p p' h := rfl
  rw [e1, e2]
  by_cases hp' : (p' : ℕ) < n + 1
  · have hp : (p : ℕ) < n + 1 := lt_of_le_of_lt (Fin.le_def.1 h) hp'
    rw [snMap_val s a (h1 p hp) (h1 p' hp') (hg h) (hf (Fin.le_def.2 (Fin.le_def.1 h))), snMap_lt _ _ h hp']
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · by_cases hp : (p : ℕ) < n + 1
    · rw [snMap_val_top s a (h1 p hp) (h2 p' hp') (hg h), snMap_mid _ _ h hp' hp]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      have e3 : s.map (homOfLE (Fin.le_last (f ⟨p, hp⟩))) =
          (hf.functor ⋙ s).map (homOfLE (Fin.le_last (⟨p, hp⟩ : Fin (n + 1)))) ≫ s.map (homOfLE (Fin.le_last (f (Fin.last n)))) := by
        change _ = s.map _ ≫ s.map _
        rw [← Functor.map_comp]
        rfl
      rw [e3]
      simp only [Category.assoc]
    · rw [snMap_top s a (hg h) (h2 p' hp') (h2 p hp), snMap_top _ _ h hp' hp]
      simp

end Chains

section Face

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E (m + 1)) {X : E} (a : s.obj (Fin.last (m + 1)) ⟶ X)

private theorem sa_lt (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : (p : ℕ) < m + 1) :
    ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) = (i.succAbove ⟨p, hp⟩ : Fin (m + 2)) := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

private theorem sa_ge (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : ¬ (p : ℕ) < m + 1) :
    ¬ ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) < m + 2 := by
  have h1 : (p : ℕ) = m + 1 := by omega
  have h2 := i.2
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp <;> omega

theorem face_snoc_castSucc (i : Fin (m + 2)) : face i.castSucc (snoc s a) = snoc (face i s) (toLast i s ≫ a) :=
  snoc_reindex s a (Fin.succAboveOrderEmb i) (Fin.succAboveOrderEmb i).monotone (Fin.succAboveOrderEmb i.castSucc)
    (Fin.succAboveOrderEmb i.castSucc).monotone (sa_lt i) (sa_ge i)

theorem gen_snoc_castSucc (i : Fin (m + 2)) :
    (⟨face i.castSucc (snoc s a), toLast i.castSucc (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E (m + 1), t.obj (Fin.last (m + 1)) ⟶ X) =
      ⟨snoc (face i s) (toLast i s ≫ a), snε _ _⟩ := by
  refine sigma_chain_eq (face_snoc_castSucc s a i) ?_
  have h0 : ¬ ((i.castSucc.succAbove (Fin.last (m + 1)) : Fin (m + 3)) : ℕ) < m + 2 := sa_ge i _ (by simp)
  have e : toLast i.castSucc (snoc s a) = eqToHom ((snObj_ge s X h0).trans (snObj_ge s X (by simp)).symm) :=
    snMap_top s a (Fin.le_last _) (by simp) h0
  rw [e]
  simp [snε]

end Face

end UpperTheory.Ru.crystallineComparison.Th
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NoethSp
section
open TopologicalSpace PrimeSpectrum

theorem UpperTheory.Et.noethSp :
    ∀ (k : Type) [Field k] (n : ℕ) (P : Set (Fin n → k) → Prop), P ∅ → (∀ s t, s ⊆ t → P t → P s) → (∀ s t, P s → P t → P (s ∪ t)) → (∀ I : Ideal (MvPolynomial (Fin n) k), I.IsPrime → ∃ g, g ∉ I ∧ P ({c | ∀ p ∈ I, MvPolynomial.eval c p = 0} ∩ {c | MvPolynomial.eval c g ≠ 0})) → P Set.univ :=
  _root_.UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitRules
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

def SplitOn {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ} (z : Fin m → (X ⟶ Z)) : Prop :=
  ∃ h : ∀ i, z i ≫ p = x, IsIso (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) :
    ∐ (fun _ : Fin m => X) ⟶ pullback p x)

abbrev awayPt (l : ℕ) (U : Type) [CommRing U] : Spec (CommRingCat.of (Localization.Away (l : U))) ⟶ Spec (CommRingCat.of U) :=
  Spec.map (CommRingCat.ofHom (algebraMap U (Localization.Away (l : U))))

structure WDat (l : ℕ) {Y : Scheme.{0}} {J : Type} (T : J → Corr l Y) : Type 1 where
  W : Scheme.{0}
  π : W ⟶ Y
  s : ∀ j, Fin (T j).d → (W ⟶ (T j).Z)
  hs : ∀ j i, s j i ≫ (T j).p = π
  gen : ∀ (X : Scheme.{0}) (w : X ⟶ W), IsUnit (l : Γ(X, ⊤)) → ∀ j, SplitOn (T j).p (w ≫ π) fun i => w ≫ s j i
  univ : ∀ (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U → ∀ (y : Spec (CommRingCat.of U) ⟶ Y)
    (z : ∀ j, Fin (T j).d → (Spec (CommRingCat.of U) ⟶ (T j).Z)), (∀ j i, z j i ≫ (T j).p = y) →
    (∀ j, SplitOn (T j).p (awayPt l U ≫ y) fun i => awayPt l U ≫ z j i) →
    ∃! w : Spec (CommRingCat.of U) ⟶ W, w ≫ π = y ∧ ∀ j i, w ≫ s j i = z j i

def WEx : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (J : Type) [Fintype J] (T : J → Corr l Y), Nonempty (WDat l T)

def SplitEx : Prop := ∀ (l : ℕ), l.Prime → ∀ (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (Localization.Away (l : U)))), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
  ∀ y : Spec (CommRingCat.of U) ⟶ Y, ∃ z : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z), (∀ i, z i ≫ T.p = y) ∧
    SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i

def SplitPerm : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  ∀ (y : Spec (CommRingCat.of U) ⟶ Y) (z z' : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z)), (∀ i, z i ≫ T.p = y) → (∀ i, z' i ≫ T.p = y) →
  (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i) → (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z' i) →
  ∃ e : Equiv.Perm (Fin T.d) → U, CompleteOrthogonalIdempotents e ∧ ∀ (σ : Equiv.Perm (Fin T.d)) (V : Type) [CommRing V] (ρ : U →+* V),
    ρ (e σ) = 1 → ∀ i, Spec.map (CommRingCat.ofHom ρ) ≫ z' i = Spec.map (CommRingCat.ofHom ρ) ≫ z (σ i)

def SplitRules : Prop :=
  (∀ {X' X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) (g : X' ⟶ X) {m : ℕ} (z : Fin m → (X ⟶ Z)), SplitOn p x z →
    (SplitOn p (g ≫ x) fun i => g ≫ z i) ∧ ∀ σ : Equiv.Perm (Fin m), SplitOn p x fun i => z (σ i)) ∧
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens), IsAffineOpen U → ∀ (B : Type) [CommRing B]
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U) (z : Fin T.d → (Spec (CommRingCat.of B) ⟶ T.Z))
    (hz : ∀ i, ⊤ ≤ z i ⁻¹ᵁ (T.p ⁻¹ᵁ U)), (∀ i, z i ≫ T.p = y) → (SplitOn T.p (awayPt l B ≫ y) fun i => awayPt l B ≫ z i) →
    letI := T.alg U
    letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
    ∃ ζ : Fin T.d → (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B), SplitsAway l ζ ∧
      ∀ i a, ζ i a = ((z i).appLE (T.p ⁻¹ᵁ U) ⊤ (hz i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom a

end UpperTheory.Ru.crystallineComparison
end
end

