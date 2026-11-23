module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanOne

variable {T : Type 1} [Category.{0} T]

lemma nat_el {C D : T ⥤ AbCx} (φ : C ⟶ D) {U V : T} (g : U ⟶ V) (n : ℤ) (c : (C.obj U).X n) :
    (φ.app V).f n ((C.map g).f n c) = (D.map g).f n ((φ.app U).f n c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

lemma comm_el {A B : AbCx} (f : A ⟶ B) (n m : ℤ) (a : A.X n) : f.f m (A.d n m a) = B.d n m (f.f n a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.comm]

lemma map_comp_el (C : T ⥤ AbCx) {U V W : T} (g : U ⟶ V) (h : V ⟶ W) (n : ℤ) (c : (C.obj U).X n) :
    (C.map (g ≫ h)).f n c = (C.map h).f n ((C.map g).f n c) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

lemma hom_zero' {A B : AddCommGrpCat.{1}} (f : A ⟶ B) : f (0 : A) = 0 := map_zero f.hom

lemma locInj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocInj Cov φ) (k m : ℤ) (hk : k + 1 = m)
    (U : T) (c : (C.obj U).X m) (hc : (C.obj U).d m (m + 1) c = 0)
    (hy : ∃ y : (D.obj U).X k, (φ.app U).f m c = (D.obj U).d k m y) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X k, (C.obj V).d k m b = (C.map g).f m c := by
  obtain rfl : k = m - 1 := by omega
  exact h m U c hc hy

lemma locSurj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocSurj Cov φ) (k n : ℤ) (hk : k + 1 = n)
    (U : T) (z : (D.obj U).X n) (hz : (D.obj U).d n (n + 1) z = 0) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X k), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d k n y := by
  obtain rfl : k = n - 1 := by omega
  exact h n U z hz

theorem cartan_one : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition]
    (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) →
    Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ →
    ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  intro T _ Cov _ C D φ hb hR hS hI
  obtain ⟨K, p, q, hbij, hd⟩ := GlobalTheory.EtC.coneEl_exists T C D φ
  have ext : ∀ n U (x y : (K.obj U).X n), (p n).app U x = (p n).app U y → (q n).app U x = (q n).app U y → x = y :=
    fun n U x y h1 h2 => (hbij n U).1 (Prod.ext h1 h2)
  have mk : ∀ n U (c : (C.obj U).X (n + 1)) (z : (D.obj U).X n), ∃ x : (K.obj U).X n, (p n).app U x = c ∧ (q n).app U x = z := by
    intro n U c z
    obtain ⟨x, hx⟩ := (hbij n U).2 (c, z)
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have dp := fun n U x => (hd n U x).1
  have dq := fun n U x => (hd n U x).2
  have natP : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (p n).app V ((K.map g).f n x) = (C.map g).f (n + 1) ((p n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (p n) g x
  have natQ : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (q n).app V ((K.map g).f n x) = (D.map g).f n ((q n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (q n) g x
  have cyc : ∀ n U (x : (K.obj U).X n), (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) = 0 →
      (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) = 0 →
      (K.obj U).d n (n + 1) x = 0 := by
    intro n U x h1 h2
    apply ext
    · rw [dp, h1, neg_zero]; exact (hom_zero' _).symm
    · rw [dq, h2]; exact (hom_zero' _).symm

  have hbK : ∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((K.obj U).X n) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b - 1, fun n hn U => ?_⟩
    have h1 := AddCommGrpCat.subsingleton_of_isZero (hb (n + 1) (by omega) U).1
    have h2 := AddCommGrpCat.subsingleton_of_isZero (hb n (by omega) U).2
    haveI : Subsingleton ((K.obj U).X n) :=
      ⟨fun x y => ext n U x y (@Subsingleton.elim _ h1 _ _) (@Subsingleton.elim _ h2 _ _)⟩
    exact AddCommGrpCat.isZero_of_subsingleton _

  have hRK : Refines Cov (fun U X a => ∀ n, WExact (term K n) a) := by
    intro U V g hg
    obtain ⟨X, a, h, hga, hQ⟩ := hR U V g hg
    refine ⟨X, a, h, hga, fun n => ?_⟩
    refine GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a Bool (fun i => cond i (term C (n + 1)) (term D n)) (term K n)
      (fun i => match i with | true => p n | false => q n) ?_ ?_
    · intro W
      constructor
      · intro x y hxy
        exact ext n W x y (congrFun hxy true) (congrFun hxy false)
      · intro f
        obtain ⟨x, hx1, hx2⟩ := mk n W (f true) (f false)
        refine ⟨x, funext fun i => ?_⟩
        cases i
        · exact hx2
        · exact hx1
    · intro i
      cases i
      · exact (hQ n).2
      · exact (hQ (n + 1)).1

  have gen : ∀ (j : ℤ) (U : T) (x : (K.obj U).X (j + 1)), (K.obj U).d (j + 1) (j + 1 + 1) x = 0 →
      ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X j, (K.obj V).d j (j + 1) y = (K.map g).f (j + 1) x := by
    intro j U x hx
    obtain ⟨c, hc⟩ : ∃ c : (C.obj U).X (j + 1 + 1), (p (j + 1)).app U x = c := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : (D.obj U).X (j + 1), (q (j + 1)).app U x = z := ⟨_, rfl⟩
    have h1 : (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 := by
      have := dp (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc] at this
      exact neg_eq_zero.mp this.symm
    have h2 : (D.obj U).d (j + 1) (j + 1 + 1) z + (φ.app U).f (j + 1 + 1) c = 0 := by
      have := dq (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc, hz] at this
      exact (add_comm _ _).trans this.symm
    obtain ⟨V₁, g₁, hg₁, b, hb⟩ := locInj' hI (j + 1) (j + 1 + 1) rfl U c h1
      ⟨-z, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h2)⟩
    obtain ⟨w, hw⟩ : ∃ w : (D.obj V₁).X (j + 1), (D.map g₁).f (j + 1) z + (φ.app V₁).f (j + 1) b = w := ⟨_, rfl⟩
    have hw0 : (D.obj V₁).d (j + 1) (j + 1 + 1) w = 0 := by
      rw [← hw, map_add (f := _), ← comm_el (D.map g₁), ← comm_el (φ.app V₁), hb, nat_el, ← map_add (f := _), h2, map_zero]
    obtain ⟨V₂, g₂, hg₂, c', y', hc', hy'⟩ := locSurj' hS j (j + 1) rfl V₁ w hw0
    obtain ⟨y, hyp, hyq⟩ := mk j V₂ (c' - (C.map g₂).f (j + 1) b) (-y')
    refine ⟨V₂, g₁ ≫ g₂, Cov.comp_mem _ _ hg₁ hg₂, y, ?_⟩
    apply ext
    · rw [dp, hyp, natP, hc, map_sub, hc', ← comm_el (C.map g₂), hb, map_comp_el, zero_sub, neg_neg]
    · rw [dq, hyp, hyq, natQ, hz, map_sub, map_neg, hy', ← hw, map_add (f := _), nat_el, map_comp_el]
      abel
  have hLK : LocExact Cov K := by
    have gen' : ∀ k n : ℤ, k + 1 = n → ∀ (U : T) (x : (K.obj U).X n), (K.obj U).d n (n + 1) x = 0 →
        ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X k, (K.obj V).d k n y = (K.map g).f n x := by
      intro k n hkn
      subst hkn
      exact gen k
    intro n U x hx
    exact gen' (n - 1) n (by omega) U x hx

  have exK : ∀ (U : T) (k n : ℤ), k + 1 = n → ∀ x : (K.obj U).X n, (K.obj U).d n (n + 1) x = 0 →
      ∃ y : (K.obj U).X k, (K.obj U).d k n y = x := by
    intro U k n hkn x hx
    obtain rfl : k = n - 1 := by omega
    exact GlobalTheory.CartanZero.cartan_zero T Cov K hbK hRK hLK U n x hx
  intro U
  constructor
  · have sg : ∀ (j : ℤ) (z : (D.obj U).X (j + 1)), (D.obj U).d (j + 1) (j + 1 + 1) z = 0 →
        ∃ (c : (C.obj U).X (j + 1)) (y : (D.obj U).X j), (C.obj U).d (j + 1) (j + 1 + 1) c = 0 ∧
          (φ.app U).f (j + 1) c = z + (D.obj U).d j (j + 1) y := by
      intro j z hz
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U 0 z
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, map_zero]) (by rw [hxp, hxq, map_zero, zero_add, hz])
      obtain ⟨y, hy⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨u, hu⟩ : ∃ u : (D.obj U).X j, (q j).app U y = u := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y = v := ⟨_, rfl⟩
      refine ⟨v, -u, ?_, ?_⟩
      · have := dp j U y
        rw [hy, hxp, hv] at this
        exact neg_eq_zero.mp this.symm
      · have := dq j U y
        rw [hy, hxq, hu, hv] at this
        rw [map_neg, this]
        abel
    have sg' : ∀ k n : ℤ, k + 1 = n → ∀ (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
        ∃ (c : (C.obj U).X n) (y : (D.obj U).X k), (C.obj U).d n (n + 1) c = 0 ∧
          (φ.app U).f n c = z + (D.obj U).d k n y := by
      intro k n hkn
      subst hkn
      exact sg k
    intro n z hz
    exact sg' (n - 1) n (by omega) z hz
  · have ij : ∀ (j : ℤ) (c : (C.obj U).X (j + 1 + 1)), (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 →
        ∀ y : (D.obj U).X (j + 1), (φ.app U).f (j + 1 + 1) c = (D.obj U).d (j + 1) (j + 1 + 1) y →
        ∃ b : (C.obj U).X (j + 1), (C.obj U).d (j + 1) (j + 1 + 1) b = c := by
      intro j c hc y hy
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U c (-y)
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, hc]) (by rw [hxp, hxq, map_neg, hy, add_neg_cancel])
      obtain ⟨y', hy'⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y' = v := ⟨_, rfl⟩
      refine ⟨-v, ?_⟩
      have := dp j U y'
      rw [hy', hxp, hv] at this
      rw [map_neg]
      exact this.symm
    have ij' : ∀ i n : ℤ, i + 1 = n → ∀ c : (C.obj U).X n, (C.obj U).d n (n + 1) c = 0 →
        ∀ y : (D.obj U).X i, (φ.app U).f n c = (D.obj U).d i n y → ∃ b : (C.obj U).X i, (C.obj U).d i n b = c := by
      intro i n hin
      subst hin
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ij j
    intro n c hc ⟨y, hy⟩
    exact ij' (n - 1) n (by omega) c hc y hy

end GlobalTheory.CartanOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushouts
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConerveNerve

variable {T : Type 1} [Category.{0} T] (Ψ : T ⥤ PShᵒᵖ) {U V : T} (g : U ⟶ V) (J : Type) [HasWidePushout U (fun _ : J => V) (fun _ => g)]

def cmp : (Ψ.obj (widePushout U (fun _ : J => V) fun _ => g)).unop ⟶
    widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun i => (Ψ.map (WidePushout.ι _ i)).unop)
    (fun i => by rw [← unop_comp, ← Ψ.map_comp]; exact congrArg (fun k => (Ψ.map k).unop) (WidePushout.arrow_ι (fun _ : J => g) i))

lemma cmp_π (i : J) : cmp Ψ g J ≫ WidePullback.π _ i = (Ψ.map (WidePushout.ι _ i)).unop := by
  simp only [cmp, WidePullback.lift_π]

lemma cmp_base : cmp Ψ g J ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  simp only [cmp, WidePullback.lift_base]

def coc : Cocone (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g) ⋙ Ψ) :=
  WidePushoutShape.mkCocone (X := op (widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop)))
    (WidePullback.base _).op (fun i => (WidePullback.π _ i).op) (fun i => by
      apply Quiver.Hom.unop_inj
      exact WidePullback.π_arrow (fun _ : J => (Ψ.map g).unop) i)

lemma isIso_cmp [PreservesColimitsOfShape (WidePushoutShape J) Ψ] : IsIso (cmp Ψ g J) := by
  let hC := isColimitOfPreserves Ψ (colimit.isColimit (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g)))
  refine ⟨(hC.desc (coc Ψ g J)).unop, ?_, ?_⟩
  · apply Quiver.Hom.op_inj
    show hC.desc (coc Ψ g J) ≫ (cmp Ψ g J).op = 𝟙 _
    apply hC.hom_ext
    intro j
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (cmp Ψ g J).op) (hC.fac (coc Ψ g J) j)).trans ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    apply Quiver.Hom.unop_inj
    rcases j with _ | i
    · exact cmp_base Ψ g J
    · exact cmp_π Ψ g J i
  · apply WidePullback.hom_ext
    · intro i
      have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) (some i))
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_π Ψ g J i)).trans ?_
      exact this.trans (Category.id_comp _).symm
    · have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) none)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_base Ψ g J)).trans ?_
      exact this.trans (Category.id_comp _).symm

end GlobalTheory.EtC.ConerveNerve

namespace GlobalTheory.EtC.ConerveNerve

theorem conerve_nerve : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), ∃ e : ((((Arrow.mk g).cechConerve ⋙ Ψ).leftOp : Spc) ⟶ (Arrow.mk (Ψ.map g).unop).cechNerve), IsIso e ∧ e ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom = lev Ψ (coAug g) := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨{ app := fun n => cmp Ψ g (Fin (n.unop.len + 1)), naturality := ?_ }, ?_, ?_⟩
  · intro m n f
    apply WidePullback.hom_ext
    · intro i
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_π Ψ g _ i)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) i =
          WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) (f.unop.toOrderHom i) :=
        WidePullback.lift_π _ _ _ _ _
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_π Ψ g _ _).symm
      change (Ψ.map (WidePushout.ι _ i) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.ι_desc)
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_base Ψ g _)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.base (fun _ : Fin ((unop n).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) =
          WidePullback.base (fun _ : Fin ((unop m).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) := by
        apply WidePullback.lift_base
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_base Ψ g _).symm
      change (Ψ.map (WidePushout.head _) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.head_desc)
  · have : ∀ n : SimplexCategoryᵒᵖ, IsIso (cmp Ψ g (Fin (n.unop.len + 1))) := fun n => by
      haveI := hΨ n.unop.len
      exact isIso_cmp Ψ g _
    exact (NatTrans.isIso_iff_isIso_app _).2 this
  · refine NatTrans.ext (funext fun n => ?_)
    exact cmp_base Ψ g _

end GlobalTheory.EtC.ConerveNerve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

def IsPow (n : ℕ) (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)) : Prop :=
  (∀ i, p i ≫ f = p 0 ≫ f) ∧ ∀ (U : Scheme.{0}) (y : Fin (n + 1) → (U ⟶ V)), (∀ i, y i ≫ f = y 0 ≫ f) →
    ∃! g : U ⟶ Z, ∀ i, g ≫ p i = y i

theorem exists_pow (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (hf : P f) (n : ℕ) : ∃ (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)), IsPow f n Z p ∧ P (p 0) := by
  induction n with
  | zero =>
    refine ⟨V, fun _ => 𝟙 V, ⟨fun _ => rfl, fun U y _ => ⟨y 0, fun i => ?_, fun g hg => ?_⟩⟩, P.id_mem V⟩
    · rw [Fin.fin_one_eq_zero i]; simp
    · simpa using hg 0
  | succ n ih =>
    obtain ⟨Z, p, ⟨hc, hu⟩, hP⟩ := ih
    let q : Fin (n + 2) → (pullback (p 0 ≫ f) f ⟶ V) :=
      Fin.snoc (α := fun _ => pullback (p 0 ≫ f) f ⟶ V) (fun j => pullback.fst _ _ ≫ p j) (pullback.snd _ _)
    have qc : ∀ j : Fin (n + 1), q j.castSucc = pullback.fst _ _ ≫ p j := fun j => by simp [q]
    have ql : q (Fin.last _) = pullback.snd _ _ := by simp [q]
    have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
    have q0 : q 0 = pullback.fst _ _ ≫ p 0 := qc 0
    refine ⟨pullback (p 0 ≫ f) f, q, ⟨fun i => ?_, fun U y hy => ?_⟩, ?_⟩
    · rw [q0]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ql, ← pullback.condition, Category.assoc]
      · rw [qc, Category.assoc, Category.assoc, hc j]
    · have h' : ∀ j : Fin (n + 1), y j.castSucc ≫ f = y (Fin.castSucc 0) ≫ f := fun j => by
        rw [hy, hz, hy]
      obtain ⟨g0, hg0, hg0u⟩ := hu U (fun j => y j.castSucc) h'
      have hw : g0 ≫ p 0 ≫ f = y (Fin.last _) ≫ f := by
        rw [← Category.assoc, hg0 0, hy (Fin.last _), hz]
      refine ⟨pullback.lift g0 (y (Fin.last _)) hw, fun i => ?_, fun g hg => ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [ql, pullback.lift_snd]
        · rw [qc, pullback.lift_fst_assoc, hg0 j]
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hg0u _ (fun j => ?_)
          rw [Category.assoc, ← qc, hg]
        · rw [pullback.lift_snd, ← ql, hg]
    · rw [q0]
      exact P.comp_mem _ _ (P.pullback_fst _ _ hf) hP

end GlobalTheory.EtC.CechRep

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

noncomputable section

def isLimitPow {n : ℕ} {Z : Scheme.{0}} {p : Fin (n + 1) → (Z ⟶ V)} (h : IsPow f n Z p) :
    IsLimit (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f))
      (p 0 ≫ f) p (fun j => h.1 j)) := by
  have hs : ∀ s : Cone (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, s.π.app (some j) ≫ f = s.π.app (some 0) ≫ f := fun s j => by
    have a : s.π.app (some j) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term j)
    have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
    rw [a, b]
  refine IsLimit.mk (fun s => (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose) (fun s j => ?_)
    (fun s m hm => ?_)
  · have hl := (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec
    cases j with
    | none =>
      have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
      change (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose ≫ (p 0 ≫ f) = s.π.app none
      rw [← Category.assoc, hl 0]
      exact b
    | some j =>
      exact hl j
  · exact (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).unique (fun j => hm (some j))
      (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec

end

end GlobalTheory.EtC.CechRep

theorem GlobalTheory.EtC.cech_level_representable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  intro P _ _ V W f hf k
  obtain ⟨Z, p, h, hP⟩ := GlobalTheory.EtC.CechRep.exists_pow f P hf k.unop.len
  have hY := isLimitOfPreserves yoneda (GlobalTheory.EtC.CechRep.isLimitPow f h)
  let D := WidePullbackShape.wideCospan (yoneda.obj W) (fun _ : Fin (k.unop.len + 1) => yoneda.obj V)
    (fun _ => yoneda.map f)
  let iso : WidePullbackShape.wideCospan W (fun _ : Fin (k.unop.len + 1) => V) (fun _ => f) ⋙ yoneda ≅ D :=
    WidePullbackShape.diagramIsoWideCospan _
  have hL := (IsLimit.postcomposeHomEquiv iso _).symm hY
  refine ⟨Z, p 0, IsLimit.conePointUniqueUpToIso hL (limit.isLimit D), hP, ?_⟩
  have := IsLimit.conePointUniqueUpToIso_hom_comp hL (limit.isLimit D) none
  change _ ≫ limit.π D none = _
  refine this.trans ?_
  change yoneda.map (p 0 ≫ f) ≫ iso.hom.app none = _
  simp [iso, WidePullbackShape.diagramIsoWideCospan]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_basic : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  intro R _
  refine ⟨fun E => (CochainComplex.isStrictlyLE_iff _ 0).2 (fun i hi => CupSpec.isZero_chains E i hi), fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [← cancel_epi (chainsXIso R E p).inv, ← Category.assoc, CupSpec.chains_map, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · rw [← Category.assoc, CupSpec.chains_d, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.isIso_chains_map_of_isIso_free (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E')
    (h : ∀ n, IsIso ((free R).map (f.app n))) : IsIso ((chains R).map f) := by
  have hw : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact h n
  have : IsIso ((chainsN R).map f) := by
    unfold chainsN
    rw [Functor.comp_map]
    infer_instance
  unfold chains
  rw [Functor.comp_map]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsQuasiIsoOfSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_quasiIso_of_sections : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ U : Scheme.{0}, QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R))).map f))) → QuasiIso ((chains R).map f) := by
  intro R _ E E' f hf
  let g := ((SimplicialObject.whiskering _ _).obj (freeP R)).map f
  let φ := (AlgebraicTopology.alternatingFaceMapComplex _).map g
  have hφ : QuasiIso φ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj t))) (Arrow.mk g)
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2 (hf t.unop)
  have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex (presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))))) (Arrow.mk g)
  have h2 : QuasiIso ((chainsN R).map f) := by
    have : QuasiIso (((presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).map φ) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).1 this
  change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  infer_instance

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphismStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc) (l : Λ), (∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ)) → ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = l → h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  first | exact @GlobalTheory.AnPer.Charts.cochain_eq_ptHom | exact GlobalTheory.AnPer.Charts.cochain_eq_ptHom | (intros; apply GlobalTheory.AnPer.Charts.cochain_eq_ptHom <;> assumption)
end

