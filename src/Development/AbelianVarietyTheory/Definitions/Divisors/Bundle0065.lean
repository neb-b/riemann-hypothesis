module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure Near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) where

  U : Over (Sp R)

  smooth : Smooth U.hom

  separated : IsSeparated U.hom

  quasiCompact : QuasiCompact U.hom

  u : pullback U.hom π ⟶ G.left

  isOpen : IsOpenImmersion u

  u_over : u ≫ G.hom = pullback.snd U.hom π

  all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ Set.range u

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def Near.Pt (N : Near π G) {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ N.U.left) (x : T ⟶ G.left) : Prop :=
  ∃ x₀ : T ⟶ pullback N.U.hom π, x₀ ≫ pullback.fst _ _ = a ∧ x₀ ≫ pullback.snd _ _ = s ∧ x₀ ≫ N.u = x

def Near.Law [GrpObj G] (N : Near π G) : Prop :=
  ∃ (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left),
    (∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) ∧ m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom ∧
    ∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G),
      N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left →
      N.Pt s (v ≫ m) (x * y).left

def Near.Datum [GrpObj G] (N : Near π G)
    (φ : (Over.pullback (pullback.fst π π)).obj G ≅ (Over.pullback (pullback.snd π π)).obj G) : Prop :=
  IsMonHom φ.hom ∧ ∀ (T : Scheme.{0}) (a : T ⟶ N.U.left) (x : T ⟶ ((Over.pullback (pullback.fst π π)).obj G).left),
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G.hom (pullback.fst π π)) →
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.snd π π) a
      (x ≫ φ.hom.left ≫ pullback.fst G.hom (pullback.snd π π))

end

def Gal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Subgroup (R' ≃+* R') where
  carrier := {σ | ∀ r, σ (ρ r) = ρ r}
  mul_mem' := fun {a b} ha hb r => by rw [RingAut.mul_apply, hb r, ha r]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha r => by
    have := congrArg a.symm (ha r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this.symm

def Gal.hom {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ : Gal ρ) : R' →+* R' := σ.1.toRingHom

def PullOver {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg ρ D D') (h : IsPullDeg s D' D') : Prop :=
  (∀ x, h.xe x = x) ∧ ∀ (b : D'.P.A.left ⟶ D.P.A.left) (c : D'.P.A.left ⟶ D'.P.A.left),
    b = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) → c = h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) → c ≫ b = b

def IsGal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Prop :=
  Finite (Gal ρ) ∧ ∀ x : R', (∀ σ ∈ Gal ρ, σ x = x) → x ∈ ρ.range

structure GalAct {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R')
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') where

  act : Gal ρ → (G'.left ⟶ G'.left)

  cart : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)

  act_one : act 1 = 𝟙 _

  act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ

  unif : ∀ σ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
    (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
    bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = act σ ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

section Char

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def EndChar (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X) : Prop :=
  ∀ (κ : Type) [Field κ] (a : R →+* κ) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (G₀ : Over (Sp κ)) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀), f₀.left ≫ φ = φ ≫ f.left →
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) m ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h

def CoordMap (D : DegPre R) (D' : DegPre V) (g : R →+* V) (ρ : D.X →+ D'.X) : Prop :=
  ∀ y r r', PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r'

def EquivMap (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (f : G ⟶ G) (f' : G' ⟶ G'), IsMonHom f → IsMonHom f' → f'.left ≫ β = β ≫ f.left →
    ∀ m m', EndChar U f m → EndChar U' f' m' → ∀ y, ρ (m y) = m' (ρ y)

end Char

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

def SharpBy (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) : Prop :=
  SiegPB c F.univ u ∧ (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

theorem sharpOver_iff (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) :
    SharpOver F W P u ↔ ∃ c pr, SharpBy F W P u c pr :=
  ⟨fun ⟨c, h, pr, h'⟩ => ⟨c, pr, h, h'⟩, fun ⟨c, pr, h, h'⟩ => ⟨c, h, pr, h'⟩⟩

def MatEnd {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (a b : Fin 8) (f : B ⟶ B) : Prop :=
  IsMonHom f ∧ ∀ w, f ≫ pr w = if w = a then pr b else 1

def MatRel (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) : Prop :=
  ∀ v, ∑ u, (W + W.transpose) v u • y' u = if v = b then ∑ u, (W + W.transpose) a u • y u else 0

def IsCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (j : O →+* R) : Prop :=
  ∃ e : AdicCompletion (maximalIdeal O) O ≃+* R, ∀ a, e (algebraMap O _ a) = j a

theorem isCpl_self (O : Type) [CommRing O] [IsLocalRing O] :
    IsCpl (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
  ⟨RingEquiv.refl _, fun _ => rfl⟩


open Classical in
def MatOn {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) : Prop :=
  IsMonHom f ∧ ∃ f₁ : ρ.P.A ⟶ ρ.P.A, MatEnd pr a b f₁ ∧
    ((Over.pullback FinalForm.u₀).map f₁).left ≫ FinalForm.φ = FinalForm.φ ≫ f.left

end GlobalTheory.Poinc.Eq8
end
end

