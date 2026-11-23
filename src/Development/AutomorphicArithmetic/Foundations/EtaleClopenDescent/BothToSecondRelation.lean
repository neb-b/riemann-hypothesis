module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Aff

structure RF where
  obj : ∀ (A : Type) [CommRing A], Type
  map : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → obj A → obj B
  map_id : ∀ {A : Type} [CommRing A] (x : obj A), map (RingHom.id A) x = x
  map_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (x : obj A),
    map (g.comp f) x = map g (map f x)
  rel : ∀ {A : Type} [CommRing A], obj A → obj A → Prop
  map_rel : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x y : obj A}, rel x y → rel (map f x) (map f y)

structure RF.Hom (X Y : RF) where
  app : ∀ (A : Type) [CommRing A], X.obj A → Y.obj A
  nat : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : X.obj A), app B (X.map f x) = Y.map f (app A x)

def RF.Hom.Rel {X Y : RF} (h : X.Hom Y) : Prop :=
  ∀ {A : Type} [CommRing A] {x y : X.obj A}, X.rel x y → Y.rel (h.app A x) (h.app A y)

def CN (X : RF) : Spc where
  obj n :=
    { obj := fun U => {x : Fin (n.unop.len + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}
      map := fun f => TypeCat.ofHom fun x =>
        ⟨fun i => X.map f.unop.appTop.hom (x.1 i), fun i j => X.map_rel _ (x.2 i j)⟩
      map_id := fun U => by
        ext x i
        exact X.map_id (x.1 i)
      map_comp := fun f g => by
        ext x i
        exact X.map_comp f.unop.appTop.hom g.unop.appTop.hom (x.1 i) }
  map θ :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => x.1 (θ.unop.toOrderHom i), fun i j => x.2 _ _⟩
      naturality := fun U V f => rfl }
  map_id n := rfl
  map_comp θ θ' := rfl

def CN.map {X Y : RF} (h : X.Hom Y) (hr : h.Rel) : CN X ⟶ CN Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => h.app _ (x.1 i), fun i j => hr (x.2 i j)⟩
      naturality := fun U V f => by
        refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext (funext fun i => ?_)
        exact h.nat f.unop.appTop.hom (x.1 i) }
  naturality n m θ := rfl

def RF.sub (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) : RF where
  obj A _ := {x : X.obj A // P x}
  map f x := ⟨X.map f x.1, hP f x.2⟩
  map_id x := Subtype.ext (X.map_id x.1)
  map_comp f g x := Subtype.ext (X.map_comp f g x.1)
  rel x y := X.rel x.1 y.1
  map_rel f _ _ h := X.map_rel f h

def RF.subι (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.sub P hP).Hom X where
  app _ _ x := x.1
  nat _ _ := rfl

theorem RF.subι_rel (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.subι P hP).Rel := fun h => h

variable (D : Type) [CommRing D]

def Vec (N : ℕ) : RF where
  obj A _ := {x : (D →+* A) × (Fin N → A) // Ideal.span (Set.range x.2) = ⊤}
  map f x := ⟨(f.comp x.1.1, f ∘ x.1.2), by rw [Set.range_comp, ← Ideal.map_span, x.2, Ideal.map_top]⟩
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel {A} _ x y := x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j
  map_rel {A B} _ _ f x y h := by
    obtain ⟨h1, u, h2⟩ := h
    refine ⟨congrArg f.comp h1, Units.map (f : A →* B) u, funext fun j => ?_⟩
    simp [h2]

variable {D}

def P2 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop :=
  Ideal.span (Set.range fun j : Fin d => x.1.2 j.castSucc) = ⊤

def P1 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop := IsUnit (x.1.2 (Fin.last d))

theorem second_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P2 x) :
    P2 ((Vec D (d + 1)).map f x) := by
  have : (Set.range fun j : Fin d => ((Vec D (d + 1)).map f x).1.2 j.castSucc) =
      f '' (Set.range fun j : Fin d => x.1.2 j.castSucc) := by
    rw [← Set.range_comp]; rfl
  rw [P2, this, ← Ideal.map_span, h, Ideal.map_top]

theorem first_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    P1 ((Vec D (d + 1)).map f x) := h.map f

variable (D)

abbrev L2 (d : ℕ) : RF := (Vec D (d + 1)).sub P2 second_property_map

abbrev L1 (d : ℕ) : RF := (Vec D (d + 1)).sub P1 first_property_map

def fstV (d : ℕ) : (L2 D d).Hom (Vec D d) where
  app _ _ x := ⟨(x.1.1.1, fun j => x.1.1.2 j.castSucc), x.2⟩
  nat _ _ := rfl


section Formal
open LateralTheory.E.t_E6Cut
variable {R : Type} [CommRing R] (F : Shv R)

end Formal

end UpperTheory.Aff

end
