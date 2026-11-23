module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0002
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} [Field K] [NumberField K]

structure GenFib (t : SAB H (Sp (𝓞 K))) where

  tK : SAB H (Sp K)

  m : SABMap tK t (spMap (algebraMap (𝓞 K) K))

  g : ℕ

  v : Fin g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v

namespace GenFib

variable {t t' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t')

structure CxFib (σ : K →+* ℂ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ F.tK.G.left
  cart : IsGrpPullback A F.tK.G (spMap σ) φ

  u : HolUnif A (F.tK.PP.L.pull φ) F.g

  Hm : Matrix (Fin F.g) (Fin F.g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ

  vC : Fin F.g → (epsR ℂ ⟶ A)
  vC_base : ∀ i, (vC i).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (F.v i).left

  W : Fin F.g → (Fin F.g → ℂ)
  diff : ∀ i, u.IsDiff (W i) (vC i)

attribute [instance] CxFib.grp



end GenFib

section Sum

variable {S : Scheme.{0}}

def sumPow {A B : Over S} [GrpObj B] {n : ℕ} (f : Fin n → (A ⟶ B)) : (∏ᶜ fun _ : Fin n => A) ⟶ B :=
  (List.ofFn fun i => Pi.π (fun _ : Fin n => A) i ≫ f i).prod

def sumMap {A A' B : Over S} [GrpObj B] {p q : ℕ} (f : Fin p → (A ⟶ B)) (f' : Fin q → (A' ⟶ B)) :
    (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A') ⟶ B :=
  (fst _ _ ≫ sumPow f) * (snd _ _ ≫ sumPow f')

def IsFinFlatSurj {X Y : Over S} (f : X ⟶ Y) : Prop := IsFinite f.left ∧ Flat f.left ∧ Surjective f.left

def IsLinHom {t t' : SAB H S} (f : t.G ⟶ t'.G) : Prop :=
  IsMonHom f ∧ ∀ a : 𝓞 E, t.act.act a ≫ f = f ≫ t'.act.act a

def PolId {t t' : SAB H S} (f : t.G ⟶ t'.G) (h : 𝓞 E) : Prop :=
  WeilEq t'.PP.L f f t.PP.L (t.act.act h) (𝟙 t.G)

end Sum

structure CMObj (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (p q : ℕ) where

  A : SAB H (Sp (𝓞 K))

  A' : SAB H (Sp (𝓞 K))

  B : SAB H (Sp (𝓞 K))
  prinA : IsPrincipal A
  prinA' : IsPrincipal A'
  prinB : IsPrincipal B
  sigA : HasSig H 1 0 A.act ρ
  sigA' : HasSig H 0 1 A'.act ρ
  sigB : HasSig H p q B.act ρ

  ph : Fin p → (A.G ⟶ B.G)

  ph' : Fin q → (A'.G ⟶ B.G)
  lin : ∀ i, IsLinHom (ph i)
  lin' : ∀ j, IsLinHom (ph' j)
  isog : IsFinFlatSurj (sumMap ph ph')

  h : Fin p → 𝓞 E

  h' : Fin q → 𝓞 E
  pol : ∀ i, PolId (ph i) (h i)
  pol' : ∀ j, PolId (ph' j) (h' j)

namespace CMObj

variable {ρ : 𝓞 K} {p q : ℕ} (X : CMObj H K ρ p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres
