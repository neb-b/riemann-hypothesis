module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) := by
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective d hd, ?_, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  · exact h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
      (Scheme.ΓSpecIso R₀).symm (Scheme.ΓSpecIso_inv_naturality a) (Scheme.ΓSpecIso_inv_naturality b)
      (Scheme.ΓSpecIso_inv_naturality c) (Scheme.ΓSpecIso_inv_naturality d)


end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU

variable {p : ℕ} [Fact p.Prime]

def Datum.inv (D : Datum p) (x : D.O) : D.O := (D.star x).unop

def Datum.plat (D : Datum p) : PLat D.O D.inv where
  La := D.La
  fin := D.finLa
  free := D.freeLa
  EF := (2 : ℤ) • D.EF
  alt x := by simp [D.alt]
  nondeg x h := D.nondeg (by
    ext y
    have := h y
    simpa using this)
  adj a x y := by simp [D.adj, Datum.inv]

def Datum.g (D : Datum p) : ℕ := D.m * D.n * Module.finrank ℚ D.F / 2

def HalfPerf {O : Type} [Ring O] {bar : O → O} (p : ℕ) (D' : PLat O bar) : Prop :=
  ∃ E₁ : LinearMap.BilinForm ℤ D'.La, D'.EF = (2 : ℤ) • E₁ ∧
    ∃ e : ℕ, e.Coprime p ∧ ∀ f : D'.La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e • f

def Datum.Cls (D : Datum p) (N : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La) : Prop :=
  Genus p N D.plat D' t ∧ HalfPerf p D'


open Classical in
def Base.IsType {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, σ (b.t i c) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ σ b.ρ), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (σ (b.t i c)))

def Obj.fam {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) :
    Fam R D.O D.La D.g where
  X := S
  s := s
  A := o.A
  ab := o.ab
  dim := h
  act := o.act.act
  hom := o.act.hom
  act_one := o.act.one
  act_mul := o.act.mul
  act_add := o.act.add
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  isLB := hL
  ample := o.ample
  eta := o.eta

def Model.Uniformised {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} (M : Model b N) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∃ h hL, Nonempty (Unif (M.univ.fam h hL) σ ρ N (D.Cls N))

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {X Y : Scheme.{0}}

structure IsOn (W : X.Opens) (L : LB X) : Prop where
  le : ∀ a, L.U a ≤ W
  cov : ∀ x ∈ W, ∃ a, x ∈ L.U a
  coc : ∀ (x : X) (a b c : L.ι), x ∈ L.U a → x ∈ L.U b → x ∈ L.U c →
    gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b c) = gm (𝟙 X) x _ (L.g a c)

abbrev Cmp (W : X.Opens) (L M : LB X) : Type := ∀ (a : L.ι) (b : M.ι), Γ(X, W ⊓ (L.U a ⊓ M.U b))ˣ

def IsoOn (W : X.Opens) (L M : LB X) (w : Cmp W L M) : Prop :=
  ∀ x ∈ W, ∀ (a a' : L.ι) (b b' : M.ι), x ∈ L.U a → x ∈ L.U a' → x ∈ M.U b → x ∈ M.U b' →
    gm (𝟙 X) x _ (w a b) * gm (𝟙 X) x _ (M.g b b') = gm (𝟙 X) x _ (L.g a a') * gm (𝟙 X) x _ (w a' b')

abbrev RigD (e : Y ⟶ X) (L : LB X) : Type := ∀ a : L.ι, Γ(Y, e ⁻¹ᵁ L.U a)ˣ

def RigOn (e : Y ⟶ X) (L : LB X) (r : RigD e L) : Prop :=
  ∀ (y : Y) (a b : L.ι), e y ∈ L.U a → e y ∈ L.U b →
    gm (𝟙 Y) y _ (r a) = gm e y _ (L.g a b) * gm (𝟙 Y) y _ (r b)

def Norm (e : Y ⟶ X) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : RigD e L) (r' : RigD e M) : Prop :=
  ∀ (y : Y) (a : L.ι) (b : M.ι), e y ∈ W → e y ∈ L.U a → e y ∈ M.U b →
    gm e y _ (w a b) * gm (𝟙 Y) y _ (r' b) = gm (𝟙 Y) y _ (r a)

def FnBij (p : X ⟶ Y) : Prop := ∀ V : Y.Opens, Function.Bijective (p.app V).hom

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def AddCls {T : Over S} (c : Pic (A ⊗ T).left) : Prop :=
  ∀ (Z : Over S) (a a' : Z ⟶ A) (t : Z ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c

theorem AddCls.pull {T T' : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) (u : T' ⟶ T) :
    AddCls A (CechPic.pull (A ◁ u).left c) := fun Z a a' t ↦ by
  simpa only [← pull_comp, ← Over.comp_left, lift_whiskerLeft] using h Z a a' (t ≫ u)

def addF : (Over S)ᵒᵖ ⥤ Type 1 where
  obj T := {c : Pic (A ⊗ T.unop).left // AddCls A c}
  map u := TypeCat.ofHom fun c ↦ ⟨CechPic.pull (A ◁ u.unop).left c.1, c.2.pull A u.unop⟩
  map_id T := by
    ext c
    change CechPic.pull (A ◁ 𝟙 T.unop).left c.1 = c.1
    rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]
  map_comp u v := by
    ext c
    change CechPic.pull (A ◁ (v.unop ≫ u.unop)).left c.1 =
      CechPic.pull (A ◁ v.unop).left (CechPic.pull (A ◁ u.unop).left c.1)
    rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem addF_map_val {T T' : Over S} (u : T' ⟶ T) (c : (addF A).obj (Opposite.op T)) :
    ((addF A).map u.op c).1 = CechPic.pull (A ◁ u).left c.1 := rfl

variable {A}

def famCls {T : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) : (addF A).obj (Opposite.op T) :=
  ⟨cls N h.isLB, (isAdditive_iff h.isLB).1 h.add⟩

theorem famCls_surj {T : Over S} (c : (addF A).obj (Opposite.op T)) :
    ∃ (N : LB (A ⊗ T).left) (h : Fam A N), famCls h = c := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact ⟨N, ⟨hN, (isAdditive_iff hN).2 hc⟩, rfl⟩


omit [GrpObj A] in
theorem whiskerLeft_eq_lift {T T' : Over S} (u : T' ⟶ T) : A ◁ u = lift (fst A T') (snd A T' ≫ u) := by
  ext <;> simp

theorem same_iff_map {T U Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M)
    (y : Z ⟶ T) (u : Z ⟶ U) : Same A N M y u ↔ (addF A).map y.op (famCls hN) = (addF A).map u.op (famCls hM) := by
  refine (same_iff hN.isLB hM.isLB y u).trans (Iff.trans ?_ Subtype.ext_iff.symm)
  rw [addF_map_val, addF_map_val, whiskerLeft_eq_lift, whiskerLeft_eq_lift]
  rfl

end GlobalTheory.PicGlue
end
end

